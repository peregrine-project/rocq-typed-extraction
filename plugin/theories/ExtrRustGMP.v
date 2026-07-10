(** Rust numeric remap targeting GMP arbitrary-precision integers via the
    [rug] crate ([rug::Integer], a safe wrapper around GMP/MPFR).

    This is the GMP analogue of [ExtrRustCheckedArith] / [ExtrRustUncheckedArith]:
    it maps [nat]/[positive]/[N]/[Z] to [rug::Integer] and their arithmetic to
    native GMP operations, so extracted arithmetic runs on GMP integers rather
    than unary Peano / binary-inductive towers.  Unlike the u64/i64 remaps this is *faithful*
    (unbounded), at the cost of GMP's heap representation.

    Representation note (must be validated by a build): [rug::Integer] owns a
    GMP allocation and is [Clone] but NOT [Copy], whereas the u64 remap relies on
    the target type being [Copy].  The op bodies below are self-contained; the
    only risk is at generated call sites that use a numeric variable
    non-linearly, which may require [.clone()] insertion.  The matching runtime
    preamble is [rust_gmp_preamble] (see RustBackend.v).  Cargo dependency:
    [rug = "1"]. *)

From Stdlib Require Import Extraction.
From Stdlib Require Import ZArith.

(* zero = Integer::new(); one = Integer::from(1); successors/bit-builders and
   the eliminators are provided by the GMP preamble (see rust_gmp_preamble). *)
Extract Inductive nat => "rug::Integer" ["rug::Integer::new()" "__nat_succ"] "__nat_elim!".
Extract Inductive positive => "rug::Integer" ["__pos_onebit" "__pos_zerobit" "rug::Integer::from(1)"] "__pos_elim!".
Extract Inductive N => "rug::Integer" ["rug::Integer::new()" "__N_frompos"] "__N_elim!".
Extract Inductive Z => "rug::Integer" ["rug::Integer::new()" "__Z_frompos" "__Z_fromneg"] "__Z_elim!".
Extract Inductive comparison =>
  "std::cmp::Ordering"
    ["std::cmp::Ordering::Equal"
     "std::cmp::Ordering::Less"
     "std::cmp::Ordering::Greater"].

(* --- positive --- *)
Extract Constant Corelib.BinNums.PosDef.Pos.add => "fn ##name##(&'a self, a: rug::Integer, b: rug::Integer) -> rug::Integer { rug::Integer::from(a + b) }".
Extract Constant Corelib.BinNums.PosDef.Pos.succ => "fn ##name##(&'a self, a: rug::Integer) -> rug::Integer { a + 1 }".
Extract Constant Stdlib.PArith.BinPosDef.Pos.pred => "fn ##name##(&'a self, a: rug::Integer) -> rug::Integer { rug::Integer::from(&a - 1).max(rug::Integer::from(1)) }".
Extract Constant Corelib.BinNums.PosDef.Pos.sub => "fn ##name##(&'a self, a: rug::Integer, b: rug::Integer) -> rug::Integer { rug::Integer::from(a - b) }".
Extract Constant Corelib.BinNums.PosDef.Pos.mul => "fn ##name##(&'a self, a: rug::Integer, b: rug::Integer) -> rug::Integer { rug::Integer::from(a * b) }".
Extract Constant Stdlib.PArith.BinPosDef.Pos.min => "fn ##name##(&'a self, a: rug::Integer, b: rug::Integer) -> rug::Integer { a.min(b) }".
Extract Constant Stdlib.PArith.BinPosDef.Pos.max => "fn ##name##(&'a self, a: rug::Integer, b: rug::Integer) -> rug::Integer { a.max(b) }".
Extract Constant Corelib.BinNums.PosDef.Pos.eqb => "fn ##name##(&'a self, a: rug::Integer, b: rug::Integer) -> bool { a == b }".
Extract Constant Corelib.BinNums.PosDef.Pos.compare =>
"fn ##name##(&'a self, a: rug::Integer, b: rug::Integer) -> std::cmp::Ordering { a.cmp(&b) }".

(* --- N --- *)
Extract Constant Stdlib.NArith.BinNatDef.N.add => "fn ##name##(&'a self, a: rug::Integer, b: rug::Integer) -> rug::Integer { rug::Integer::from(a + b) }".
Extract Constant Stdlib.NArith.BinNatDef.N.succ => "fn ##name##(&'a self, a: rug::Integer) -> rug::Integer { a + 1 }".
Extract Constant Stdlib.NArith.BinNatDef.N.pred => "fn ##name##(&'a self, a: rug::Integer) -> rug::Integer { rug::Integer::from(&a - 1).max(rug::Integer::new()) }".
Extract Constant Stdlib.NArith.BinNatDef.N.sub => "fn ##name##(&'a self, a: rug::Integer, b: rug::Integer) -> rug::Integer { rug::Integer::from(a - b).max(rug::Integer::new()) }".
Extract Constant Stdlib.NArith.BinNatDef.N.mul => "fn ##name##(&'a self, a: rug::Integer, b: rug::Integer) -> rug::Integer { rug::Integer::from(a * b) }".
Extract Constant Stdlib.NArith.BinNatDef.N.div => "fn ##name##(&'a self, a: rug::Integer, b: rug::Integer) -> rug::Integer { if b == 0 { rug::Integer::new() } else { rug::Integer::from(a / b) } }".
Extract Constant Stdlib.NArith.BinNatDef.N.modulo => "fn ##name##(&'a self, a: rug::Integer, b: rug::Integer) -> rug::Integer { if b == 0 { a } else { rug::Integer::from(a % b) } }".
Extract Constant Stdlib.NArith.BinNatDef.N.min => "fn ##name##(&'a self, a: rug::Integer, b: rug::Integer) -> rug::Integer { a.min(b) }".
Extract Constant Stdlib.NArith.BinNatDef.N.max => "fn ##name##(&'a self, a: rug::Integer, b: rug::Integer) -> rug::Integer { a.max(b) }".
Extract Constant Stdlib.NArith.BinNatDef.N.eqb => "fn ##name##(&'a self, a: rug::Integer, b: rug::Integer) -> bool { a == b }".
Extract Constant Stdlib.NArith.BinNatDef.N.compare =>
"fn ##name##(&'a self, a: rug::Integer, b: rug::Integer) -> std::cmp::Ordering { a.cmp(&b) }".

(* --- Z --- *)
Extract Constant Corelib.BinNums.IntDef.Z.add => "fn ##name##(&'a self, a: rug::Integer, b: rug::Integer) -> rug::Integer { rug::Integer::from(a + b) }".
Extract Constant Stdlib.ZArith.BinIntDef.Z.succ => "fn ##name##(&'a self, a: rug::Integer) -> rug::Integer { a + 1 }".
Extract Constant Stdlib.ZArith.BinIntDef.Z.pred => "fn ##name##(&'a self, a: rug::Integer) -> rug::Integer { a - 1 }".
Extract Constant Corelib.BinNums.IntDef.Z.sub => "fn ##name##(&'a self, a: rug::Integer, b: rug::Integer) -> rug::Integer { rug::Integer::from(a - b) }".
Extract Constant Corelib.BinNums.IntDef.Z.mul => "fn ##name##(&'a self, a: rug::Integer, b: rug::Integer) -> rug::Integer { rug::Integer::from(a * b) }".
Extract Constant Corelib.BinNums.IntDef.Z.opp => "fn ##name##(&'a self, a: rug::Integer) -> rug::Integer { -a }".
Extract Constant Corelib.BinNums.IntDef.Z.min => "fn ##name##(&'a self, a: rug::Integer, b: rug::Integer) -> rug::Integer { a.min(b) }".
Extract Constant Corelib.BinNums.IntDef.Z.max => "fn ##name##(&'a self, a: rug::Integer, b: rug::Integer) -> rug::Integer { a.max(b) }".
Extract Constant Corelib.BinNums.IntDef.Z.eqb => "fn ##name##(&'a self, a: rug::Integer, b: rug::Integer) -> bool { a == b }".
(* Rocq Z.div/Z.modulo round toward -inf; rug's Div rounds toward zero.  Use
   euclidean division (div_rem_euc / rem_euc) to match Rocq semantics. *)
Extract Constant Corelib.BinNums.IntDef.Z.div =>
"fn ##name##(&'a self, a: rug::Integer, b: rug::Integer) -> rug::Integer { if b == 0 { rug::Integer::new() } else { a.div_floor(b) } }".
Extract Constant Corelib.BinNums.IntDef.Z.modulo =>
"fn ##name##(&'a self, a: rug::Integer, b: rug::Integer) -> rug::Integer { if b == 0 { a } else { a.rem_floor(b) } }".
Extract Constant Corelib.BinNums.IntDef.Z.compare =>
"fn ##name##(&'a self, a: rug::Integer, b: rug::Integer) -> std::cmp::Ordering { a.cmp(&b) }".
Extract Constant Corelib.BinNums.IntDef.Z.of_N =>
"fn ##name##(&'a self, a: rug::Integer) -> rug::Integer { a }".
Extract Constant Stdlib.ZArith.BinIntDef.Z.abs_N => "fn ##name##(&'a self, a: rug::Integer) -> rug::Integer { a.abs() }".

(* --- nat (structural stdlib ops; hottest path for the slow benchmarks) ---
   NOTE: verify these kernames against your Rocq/MetaRocq version before relying
   on them (Rocq 9 split Init between Corelib and Stdlib).  Remapping these is
   what turns O(n) nat arithmetic into single GMP operations. *)
Extract Constant Corelib.Init.Nat.add => "fn ##name##(&'a self, a: rug::Integer, b: rug::Integer) -> rug::Integer { rug::Integer::from(a + b) }".
Extract Constant Corelib.Init.Nat.mul => "fn ##name##(&'a self, a: rug::Integer, b: rug::Integer) -> rug::Integer { rug::Integer::from(a * b) }".
Extract Constant Corelib.Init.Nat.sub => "fn ##name##(&'a self, a: rug::Integer, b: rug::Integer) -> rug::Integer { rug::Integer::from(a - b).max(rug::Integer::new()) }".
Extract Constant Corelib.Init.Nat.eqb => "fn ##name##(&'a self, a: rug::Integer, b: rug::Integer) -> bool { a == b }".
Extract Constant Corelib.Init.Nat.leb => "fn ##name##(&'a self, a: rug::Integer, b: rug::Integer) -> bool { a <= b }".
Extract Constant Corelib.Init.Nat.ltb => "fn ##name##(&'a self, a: rug::Integer, b: rug::Integer) -> bool { a < b }".
Extract Constant Corelib.Init.Nat.compare =>
"fn ##name##(&'a self, a: rug::Integer, b: rug::Integer) -> std::cmp::Ordering { a.cmp(&b) }".
Extract Constant Corelib.Init.Nat.max => "fn ##name##(&'a self, a: rug::Integer, b: rug::Integer) -> rug::Integer { a.max(b) }".
Extract Constant Corelib.Init.Nat.min => "fn ##name##(&'a self, a: rug::Integer, b: rug::Integer) -> rug::Integer { a.min(b) }".
Extract Constant Corelib.Init.Nat.div => "fn ##name##(&'a self, a: rug::Integer, b: rug::Integer) -> rug::Integer { if b == 0 { rug::Integer::new() } else { rug::Integer::from(a / b) } }".
Extract Constant Corelib.Init.Nat.modulo => "fn ##name##(&'a self, a: rug::Integer, b: rug::Integer) -> rug::Integer { if b == 0 { a } else { rug::Integer::from(a % b) } }".
