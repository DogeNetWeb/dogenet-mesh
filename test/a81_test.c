// a81_test.c — A8-1, the post-transfer floor race (sp_state_admit epoch pin).
//
// Legacy rule: when a held name changes owner, the floor jumps to the
// RECEIVER's tip - SP_STATE_REORG. The new owner's first ops are anchored at the
// PUBLISHER's tip - SP_STATE_REORG, so if they reach a node whose tip is one or
// more blocks further on they are rejected "anchor below floor" for good.
// A8-1 (from SpChainOracle.epoch_floor_from): the floor is anchored to the
// epoch's start height E on chain, E - SP_STATE_REORG - 1, identical on every
// node, so no arrival delay can strand those ops.
//
// Covers: the race (legacy reproduces, A8-1 admits) for delays 0..20 blocks;
// the activation boundary; legacy identity below activation (randomised
// differential: the same op/transfer stream through the legacy oracle and
// through an A8-1 oracle whose activation is above every epoch => byte-equal
// stores); and that the new floor opens nothing for the PREVIOUS owner (owner
// key, delegated hot key, ops pre-signed before the transfer, A->B->A replays)
// or for the new owner's ops anchored below the new floor.
#include "dogenet/state.h"
#include "dogenet/crypto.h"

#include <sqlite3.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

static int g_fail, g_ok;
#define CK(c, m) do { if (c) { printf("  ok   %s\n", m); g_ok++; } \
                      else { printf("  FAIL %s\n", m); g_fail++; } } while (0)

// ── fake chain: one name, settable owner / tip / epoch start ─────────────────
typedef struct { uint8_t owner[20]; int owned; uint32_t tip; int64_t epoch; } Chain;
static int f_owner(void *u, const char *name, uint8_t out[20]) {
    Chain *c = u; (void)name;
    if (!c->owned) return 0;
    memcpy(out, c->owner, 20); return 1;
}
static int f_header(void *u, uint32_t h, uint8_t out[32]) {
    Chain *c = u;
    if (h > c->tip) return 0;
    uint8_t seed[8] = { 'h','d','r',0, (uint8_t)h, (uint8_t)(h >> 8), (uint8_t)(h >> 16), (uint8_t)(h >> 24) };
    sp_sha256(seed, sizeof seed, out); return 1;
}
static uint32_t f_tip(void *u) { return ((Chain *)u)->tip; }
static int64_t f_epoch(void *u, const char *name) { (void)name; return ((Chain *)u)->epoch; }
static SpChainOracle legacy(Chain *c) {          // a pre-A8-1 host: the two new fields left zero
    SpChainOracle o = { .u = c, .owner_now = f_owner, .header_at = f_header, .tip = f_tip }; return o;
}
static SpChainOracle a81(Chain *c, uint32_t from) {
    SpChainOracle o = { c, f_owner, f_header, f_tip, f_epoch, from }; return o;
}

static void testkey(const char *seed, uint8_t priv[32], uint8_t pub[33]) {
    sp_sha256((const uint8_t *)seed, strlen(seed), priv);
    while (!sp_pubkey(priv, pub)) sp_sha256(priv, 32, priv);
}
typedef struct { uint8_t priv[32], pub[33], h160[20]; } Key;
static Key mk(const char *s) { Key k; testkey(s, k.priv, k.pub); sp_hash160(k.pub, 33, k.h160); return k; }

// build one op (signed now, anchored at `anchor` with the canonical header hash)
static int build(uint8_t op, const char *key, const char *val, uint32_t anchor, const Key *k,
                 int ct, const uint8_t *cert, int cl, uint8_t *blob) {
    uint8_t ah[32];
    uint8_t seed[8] = { 'h','d','r',0, (uint8_t)anchor, (uint8_t)(anchor >> 8), (uint8_t)(anchor >> 16), (uint8_t)(anchor >> 24) };
    sp_sha256(seed, sizeof seed, ah);
    return sp_state_op_build(op, "zone", (const uint8_t *)key, key ? (int)strlen(key) : 0,
                             (const uint8_t *)val, val ? (int)strlen(val) : 0, anchor, ah,
                             k->priv, k->pub, ct, cert, cl, blob, SP_STATE_OP_MAX);
}
static int admit(SpState *st, const SpChainOracle *o, const uint8_t *blob, int n, char *err) {
    err[0] = 0;
    return sp_state_admit(st, o, 8192, 0x20, blob, n, err, 128);
}
static int emit(SpState *st, const SpChainOracle *o, uint8_t op, const char *key, const char *val,
                uint32_t anchor, const Key *k, char *err) {
    uint8_t blob[SP_STATE_OP_MAX];
    int n = build(op, key, val, anchor, k, SP_CERT_NONE, NULL, 0, blob);
    if (n < 0) { strcpy(err, "build"); return -99; }
    return admit(st, o, blob, n, err);
}
static uint32_t floor_of(const char *path) {
    sqlite3 *db; uint32_t f = 0; sqlite3_stmt *q;
    sqlite3_open_v2(path, &db, SQLITE_OPEN_READONLY, NULL);
    if (sqlite3_prepare_v2(db, "SELECT floor FROM st_names WHERE name='zone'", -1, &q, NULL) == SQLITE_OK) {
        if (sqlite3_step(q) == SQLITE_ROW) f = (uint32_t)sqlite3_column_int64(q, 0);
        sqlite3_finalize(q);
    }
    sqlite3_close(db); return f;
}
// canonical dump of a store file: every st_names + st_rows column, ordered
static char *dump(const char *path) {
    sqlite3 *db; sqlite3_open_v2(path, &db, SQLITE_OPEN_READONLY, NULL);
    size_t cap = 1 << 20, n = 0; char *out = malloc(cap); out[0] = 0;
    const char *qs[] = { "SELECT name,hex(owner),floor,sum_bytes,hex(clear_id),hex(clear_blob) FROM st_names ORDER BY name",
                         "SELECT name,hex(key),op,anchor,hex(op_id),hex(blob) FROM st_rows ORDER BY name,key" };
    for (int i = 0; i < 2; i++) {
        sqlite3_stmt *q;
        if (sqlite3_prepare_v2(db, qs[i], -1, &q, NULL) != SQLITE_OK) continue;
        while (sqlite3_step(q) == SQLITE_ROW) {
            for (int c = 0; c < sqlite3_column_count(q); c++) {
                const char *t = (const char *)sqlite3_column_text(q, c);
                size_t l = t ? strlen(t) : 4;
                if (n + l + 4 > cap) { cap *= 2; out = realloc(out, cap); }
                n += (size_t)sprintf(out + n, "%s|", t ? t : "NULL");
            }
            out[n++] = '\n'; out[n] = 0;
        }
        sqlite3_finalize(q);
    }
    sqlite3_close(db); return out;
}
static char g_tmp[64];
static const char *tmpstore(const char *tag) {
    snprintf(g_tmp, sizeof g_tmp, "/tmp/a81_test_%d_%s.db", (int)getpid(), tag);
    unlink(g_tmp); return g_tmp;
}

int main(void) {
    Key A = mk("a81-alice"), B = mk("a81-bob"), H = mk("a81-hot"), C = mk("a81-carol");
    char err[128], m[256];
    const uint32_t E = 2000;                       // the transfer block

    // ── 1. the race, by arrival delay d (receiver tip = E + d) ───────────────
    printf("-- 1. race: new owner's first op anchored at publisher tip E - REORG, receiver at E + d --\n");
    int legacy_rej = 0, a81_rej = 0;
    for (uint32_t d = 0; d <= 20; d++) {
        for (int mode = 0; mode < 2; mode++) {
            char p[64]; snprintf(p, sizeof p, "%s", tmpstore(mode ? "race_new" : "race_old"));
            SpState *st = sp_state_open(p);
            Chain ch = { {0}, 1, E - 1, 1000 }; memcpy(ch.owner, A.h160, 20);
            SpChainOracle o = mode ? a81(&ch, 1) : legacy(&ch);
            int r0 = emit(st, &o, SP_OP_PUT, "www", "alice", E - 1 - SP_STATE_REORG, &A, err);
            ch.tip = E + d; memcpy(ch.owner, B.h160, 20); ch.epoch = E;                  // transfer at E
            int r = emit(st, &o, SP_OP_PUT, "www", "bob", E - SP_STATE_REORG, &B, err);     // signed at pub tip E
            if (mode == 0 && r != 1) legacy_rej++;
            if (mode == 1 && r != 1) a81_rej++;
            if (d == 0 || d == 1 || d == 20) {
                snprintf(m, sizeof m, "%s d=%u: alice seeded (%d), bob's first op -> %d%s%s (floor %u)",
                         mode ? "A8-1  " : "legacy", d, r0, r, r == 1 ? "" : " ", r == 1 ? "" : err, floor_of(p));
                CK(r0 == 1 && (mode ? r == 1 : (d == 0 ? r == 1 : (r == 0 && !strcmp(err, "anchor below floor")))), m);
            }
            sp_state_close(st); unlink(p);
        }
    }
    snprintf(m, sizeof m, "delays 0..20: legacy rejects %d/21 (every d >= 1), A8-1 rejects %d/21", legacy_rej, a81_rej);
    CK(legacy_rej == 20 && a81_rej == 0, m);

    // ── 2. CLEAR as the new owner's first op ─────────────────────────────────
    printf("-- 2. CLEAR as the new owner's first op (same tip as the publisher) --\n");
    for (int mode = 0; mode < 2; mode++) {
        const char *p = tmpstore("clear"); SpState *st = sp_state_open(p);
        Chain ch = { {0}, 1, E - 1, 1000 }; memcpy(ch.owner, A.h160, 20);
        SpChainOracle o = mode ? a81(&ch, 1) : legacy(&ch);
        emit(st, &o, SP_OP_PUT, "www", "alice", E - 7, &A, err);
        ch.tip = E; memcpy(ch.owner, B.h160, 20); ch.epoch = E;
        int r = emit(st, &o, SP_OP_CLEAR, NULL, NULL, E - SP_STATE_REORG, &B, err);
        snprintf(m, sizeof m, "%s: first-op CLEAR -> %d %s", mode ? "A8-1  " : "legacy", r, err);
        CK(mode ? r == 1 : (r == 0 && strstr(err, "floor")), m);
        sp_state_close(st); unlink(p);
    }

    // ── 3. activation boundary ───────────────────────────────────────────────
    printf("-- 3. activation boundary (epoch_floor_from = F) --\n");
    struct { uint32_t from; int64_t e; int expect_new; const char *what; } bc[] = {
        { E + 1, E,  0, "E = F-1  -> legacy floor" },
        { E,     E,  1, "E = F    -> A8-1 floor" },
        { E - 1, E,  1, "E = F+1  -> A8-1 floor" },
        { 0,     E,  0, "F = 0    -> legacy (disabled)" },
        { 1,     -1, 0, "E unknown (-1) -> legacy" },
        { 1,     E + 9, 0, "E above the oracle's tip (inconsistent) -> legacy" },
    };
    for (unsigned i = 0; i < sizeof bc / sizeof bc[0]; i++) {
        Chain ch = { {0}, 1, E + 3, bc[i].e }; memcpy(ch.owner, B.h160, 20);
        SpChainOracle o = a81(&ch, bc[i].from);
        uint32_t f = sp_state_epoch_floor(&o, "zone");
        uint32_t want = bc[i].expect_new ? E - SP_STATE_REORG - 1 : E + 3 - SP_STATE_REORG;
        snprintf(m, sizeof m, "%s: floor %u (want %u)", bc[i].what, f, want);
        CK(f == want, m);
    }
    { Chain ch = { {0}, 1, E + 3, E }; SpChainOracle o = legacy(&ch);
      CK(sp_state_epoch_floor(&o, "zone") == E + 3 - SP_STATE_REORG, "pre-A8-1 initializer (new fields zero) -> legacy floor"); }
    { Chain ch = { {0}, 1, 3, 2 }; SpChainOracle o = a81(&ch, 1);
      CK(sp_state_epoch_floor(&o, "zone") == 0, "young chain: E <= REORG+1 -> floor 0 (no underflow)"); }

    // ── 4. legacy identity below activation: randomised differential ─────────
    printf("-- 4. below activation the store is byte-identical to the legacy rule --\n");
    {
        int runs = 40, same = 0, ops_total = 0, rej_total = 0;
        for (int run = 0; run < runs; run++) {
            const char *pa = "/tmp/a81_test_diff_old.db", *pb = "/tmp/a81_test_diff_new.db";
            unlink(pa); unlink(pb);
            SpState *sa = sp_state_open(pa), *sb = sp_state_open(pb);
            Chain ca = { {0}, 1, 1000, 1000 }, cb;
            memcpy(ca.owner, A.h160, 20); cb = ca;
            SpChainOracle oa = legacy(&ca), ob = a81(&cb, 1000000);     // activation above every epoch
            Key *who[3] = { &A, &B, &C };
            int cur = 0; srand(1234 + run);
            for (int i = 0; i < 300; i++) {
                int r = rand() % 100;
                if (r < 8) {                                              // a transfer (or lapse / reclaim)
                    ca.tip += 1 + rand() % 3;
                    if (rand() % 6 == 0) { ca.owned = !ca.owned; }
                    else { cur = rand() % 3; memcpy(ca.owner, who[cur]->h160, 20); ca.owned = 1; }
                    ca.epoch = ca.tip; cb = ca;
                    continue;
                }
                if (r < 30) { ca.tip++; cb.tip = ca.tip; continue; }      // a block
                int signer = rand() % 4 == 0 ? rand() % 3 : cur;          // mostly the owner, sometimes not
                uint32_t lag = (uint32_t)(rand() % 12);
                uint32_t anchor = ca.tip > SP_STATE_REORG + lag ? ca.tip - SP_STATE_REORG - lag + (uint32_t)(rand() % 8) : 1;
                uint8_t opc = (uint8_t)(r < 80 ? SP_OP_PUT : r < 92 ? SP_OP_DEL : SP_OP_CLEAR);
                char k[8]; snprintf(k, sizeof k, "k%d", rand() % 5);
                char v[16]; snprintf(v, sizeof v, "v%d", i);
                uint8_t blob[SP_STATE_OP_MAX];
                int n = build(opc, opc == SP_OP_CLEAR ? NULL : k, opc == SP_OP_PUT ? v : NULL, anchor, who[signer],
                              SP_CERT_NONE, NULL, 0, blob);
                char e1[128], e2[128];
                int r1 = admit(sa, &oa, blob, n, e1), r2 = admit(sb, &ob, blob, n, e2);
                ops_total++; if (r1 != 1) rej_total++;
                if (r1 != r2 || strcmp(e1, e2)) { printf("  diverged run %d op %d: %d '%s' vs %d '%s'\n", run, i, r1, e1, r2, e2); break; }
            }
            sp_state_close(sa); sp_state_close(sb);
            char *da = dump(pa), *db = dump(pb);
            if (!strcmp(da, db)) same++;
            free(da); free(db); unlink(pa); unlink(pb);
        }
        snprintf(m, sizeof m, "%d/%d random streams (%d ops, %d rejected incl. floor rejects): identical results + byte-identical stores",
                 same, runs, ops_total, rej_total);
        CK(same == runs, m);
    }

    // ── 5. no new opening for the previous owner ─────────────────────────────
    printf("-- 5. attacks on the new floor --\n");
    {
        const char *p = tmpstore("atk"); SpState *st = sp_state_open(p);
        Chain ch = { {0}, 1, E - 1, 1000 }; memcpy(ch.owner, A.h160, 20);
        SpChainOracle o = a81(&ch, 1);
        uint8_t cert[256];
        int cl = sp_cert_build_p2pkh((const uint8_t *)"zone", 4, A.priv, H.pub, 0x20, E + 1000, cert, sizeof cert);
        // ops alice pre-signs BEFORE the transfer, at every anchor up to E-1, to race in afterwards
        uint8_t pre[16][SP_STATE_OP_MAX]; int pren[16], np = 0;
        for (uint32_t a = E - 8; a <= E - 1; a++, np++) pren[np] = build(SP_OP_PUT, "evil", "pre", a, &A, SP_CERT_NONE, NULL, 0, pre[np]);
        uint8_t hot[SP_STATE_OP_MAX]; int hn = build(SP_OP_PUT, "evil", "hot", E - 2, &H, SP_CERT_P2PKH, cert, cl, hot);
        CK(cl > 0 && emit(st, &o, SP_OP_PUT, "www", "alice", E - 7, &A, err) == 1, "alice (owner) publishes before the transfer");
        CK(admit(st, &o, hot, hn, err) == 1, "alice's delegated hot key admits before the transfer");
        ch.tip = E + 2; memcpy(ch.owner, B.h160, 20); ch.epoch = E;    // transfer to bob at E
        CK(emit(st, &o, SP_OP_PUT, "www", "bob", E - SP_STATE_REORG, &B, err) == 1, "bob's late first op admits (A8-1)");
        snprintf(m, sizeof m, "floor after the pin = E-%d (%u)", SP_STATE_REORG + 1, floor_of(p));
        CK(floor_of(p) == E - SP_STATE_REORG - 1, m);
        int pre_rej = 0;
        for (int i = 0; i < np; i++) if (admit(st, &o, pre[i], pren[i], err) == 0 && !strcmp(err, "signer is not the owner")) pre_rej++;
        snprintf(m, sizeof m, "alice's %d pre-signed ops (anchors E-8..E-1) all rejected 'signer is not the owner': %d", np, pre_rej);
        CK(pre_rej == np, m);
        int post_rej = 0;
        for (uint32_t a = E - 7; a <= E + 2; a++) if (emit(st, &o, SP_OP_PUT, "evil", "post", a, &A, err) == 0) post_rej++;
        CK(post_rej == 10, "alice's freshly signed ops at anchors E-7..tip all rejected");
        { int r = admit(st, &o, hot, hn, err);
          snprintf(m, sizeof m, "alice's hot-key (cert minted by alice) op replayed after the transfer -> %d %s", r, err);
          CK(r == 0 && strstr(err, "cert"), m); }
        { int r = emit(st, &o, SP_OP_CLEAR, NULL, NULL, E + 1, &A, err);
          snprintf(m, sizeof m, "alice's CLEAR after the transfer -> %d %s", r, err);
          CK(r == 0, m); }
        { int r = emit(st, &o, SP_OP_PUT, "old", "x", E - SP_STATE_REORG - 2, &B, err);
          snprintf(m, sizeof m, "bob's own op anchored below the new floor (E-8) -> %d %s", r, err);
          CK(r == 0 && !strcmp(err, "anchor below floor"), m); }
        uint8_t *bl = NULL; int blen = 0;
        CK(!sp_state_get(st, "zone", (const uint8_t *)"evil", 4, &bl, &blen), "no 'evil' row held"); free(bl);
        sp_state_close(st); unlink(p);
    }
    // A -> B -> A: alice's epoch-1 ops replayed into her epoch 3
    {
        int ok_both = 1;
        for (int mode = 0; mode < 2; mode++) {
            const char *p = tmpstore("aba"); SpState *st = sp_state_open(p);
            Chain ch = { {0}, 1, E - 1, 1000 }; memcpy(ch.owner, A.h160, 20);
            SpChainOracle o = mode ? a81(&ch, 1) : legacy(&ch);
            uint8_t old1[SP_STATE_OP_MAX]; int n1 = build(SP_OP_PUT, "www", "alice-epoch1", E - 7, &A, SP_CERT_NONE, NULL, 0, old1);
            admit(st, &o, old1, n1, err);
            ch.tip = E + 1; memcpy(ch.owner, B.h160, 20); ch.epoch = E;
            emit(st, &o, SP_OP_PUT, "www", "bob", E - 6, &B, err);
            ch.tip = E + 30; memcpy(ch.owner, A.h160, 20); ch.epoch = E + 30;   // back to alice 30 blocks later
            int r_new = emit(st, &o, SP_OP_PUT, "www2", "alice-epoch3", E + 24, &A, err);
            int r_old = admit(st, &o, old1, n1, err);
            snprintf(m, sizeof m, "%s A->B->A (B held 30 blocks): alice's epoch-3 op %d, her epoch-1 replay -> %d %s",
                     mode ? "A8-1  " : "legacy", r_new, r_old, err);
            CK(r_new == 1 && r_old == 0 && !strcmp(err, "anchor below floor"), m);
            if (!(r_new == 1 && r_old == 0)) ok_both = 0;
            sp_state_close(st); unlink(p);
        }
        (void)ok_both;
    }

    printf("a81_test: %d ok, %d failed\n", g_ok, g_fail);
    if (!g_fail) printf("a81_test: all passed\n");
    return g_fail ? 1 : 0;
}
