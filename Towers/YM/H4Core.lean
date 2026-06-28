/-
  H4Core.lean  —  shared mathlib-FREE engine for the H4 strata modules.

  HONEST SCOPE.  This module factors out the reusable computational engine that
  Module A (`H4_Strata_Ztau.lean`) and the later H4 strata leaves (A.1, E, …)
  all rest on: exact `ℤ[τ]` integer arithmetic (`τ² = τ + 1`), the 120-vertex
  600-cell table, the real `W(H₄)` group action, the point-stabilizer counter
  `Sym`, and the deterministic Module-A decode.  It is:

    • mathlib-FREE (Lean core only); NOT a brick; NOT in `scripts/check-towers.sh`'s
      BRICKS array; NOT a lakefile root for the lake build (compiled direct).
    • `sorry`-free / `admit`-free / `sorryAx`-free / `native_decide`-free.

  It proves NO Yang–Mills / Navier–Stokes / Riemann / Bost / BSD result.  It
  makes NO mass-gap / μ>0 / Surface-#1 claim.  `Sym(x)` is the stabilizer of a
  finite point under the linear `W(H₄)` action — PURE FINITE GEOMETRY.  It is NOT
  keyed to any prime and is causally independent of any L-function value; no
  L-function "seal" is asserted or implied.

  Every definition here is the byte-for-byte engine previously inlined in Module
  A; extracting it changes NO observed value.  See `H4_Strata_Ztau.lean` for the
  `#eval` measurements and the kernel-checked `tau_sq` / `vflat_card` facts.

  MODEL (validated against an exact Python reference, 2026-06-02):
    • `ℤ[τ]` = pairs `⟨a,b⟩` meaning `a + b·τ`, `τ² = τ + 1`.
    • `V` = the 120 unit icosians (600-cell vertices) doubled to clear halves
      (squared length 4), stored as the flat integer table `vflat` (960 = 120·8
      ints, eight per vertex `w.a w.b x.a x.b y.a y.b z.a z.b`) and reshaped by
      `chunk`; this avoids the super-linear elaboration blow-up of 120 nested
      anonymous-constructor literals.
    • `W(H₄)` (order 14400) acts on a doubled point `x` as the EXACT integer maps
      `x ↦ p·x·q̄ / 4` (proper) and `x ↦ p·x̄·q̄ / 4` (improper), `p,q ∈ V`, with
      the `±(p,q)` identification.  Fixity is the exact integer equation
      `p·x·q̄ = 4·x` (resp. `p·x̄·q̄ = 4·x`); no division is performed.
    • `decodeQuat p` is the deterministic Euclidean decode specified by Module A
      (absolute-value remainder): `m = ⌊log₃ p⌋`, `q = p / 3^m`,
      `r₀ = |q·3^m − p|`, `k = r₀ / 143`, `r = r₀ − k·143`; embedded as the
      ℤ[τ]⁴ quaternion `v(p) = (q, m·τ, k, r·τ)`.
-/

namespace H4Strata

/-- `ℤ[τ]`: the element `a + b·τ`, with `τ² = τ + 1`. -/
structure Ztau where
  a : Int
  b : Int
deriving DecidableEq, Repr

@[inline] def zadd (x y : Ztau) : Ztau := ⟨x.a + y.a, x.b + y.b⟩
@[inline] def zsub (x y : Ztau) : Ztau := ⟨x.a - y.a, x.b - y.b⟩
/-- `(a+bτ)(c+dτ) = (ac+bd) + (ad+bc+bd)τ`, using `τ² = τ+1`. -/
@[inline] def zmul (x y : Ztau) : Ztau :=
  ⟨x.a * y.a + x.b * y.b, x.a * y.b + x.b * y.a + x.b * y.b⟩
@[inline] def zscale (n : Int) (x : Ztau) : Ztau := ⟨n * x.a, n * x.b⟩

/-- Quaternion over `ℤ[τ]`. -/
structure Quat where
  w : Ztau
  x : Ztau
  y : Ztau
  z : Ztau
deriving DecidableEq, Repr

@[inline] def qconj (q : Quat) : Quat :=
  ⟨q.w, zscale (-1) q.x, zscale (-1) q.y, zscale (-1) q.z⟩
@[inline] def qscale (n : Int) (q : Quat) : Quat :=
  ⟨zscale n q.w, zscale n q.x, zscale n q.y, zscale n q.z⟩
/-- Hamilton product over `ℤ[τ]`. -/
def qmul (A B : Quat) : Quat :=
  ⟨ zsub (zsub (zsub (zmul A.w B.w) (zmul A.x B.x)) (zmul A.y B.y)) (zmul A.z B.z),
    zadd (zsub (zadd (zmul A.w B.x) (zmul A.x B.w)) (zmul A.z B.y)) (zmul A.y B.z),
    zadd (zadd (zsub (zmul A.w B.y) (zmul A.x B.z)) (zmul A.y B.w)) (zmul A.z B.x),
    zadd (zsub (zadd (zmul A.w B.z) (zmul A.x B.y)) (zmul A.y B.x)) (zmul A.z B.w) ⟩

/-- The 120 doubled icosians (600-cell vertices, squared length 4) stored flat:
    960 = 120·8 integers, eight per vertex `w.a w.b x.a x.b y.a y.b z.a z.b`. -/
def vflat : List Int := [
  1,0,1,0,1,0,1,0,
  1,0,1,0,1,0,-1,0,
  1,0,1,0,-1,0,1,0,
  1,0,1,0,-1,0,-1,0,
  1,0,-1,0,1,0,1,0,
  1,0,-1,0,1,0,-1,0,
  1,0,-1,0,-1,0,1,0,
  1,0,-1,0,-1,0,-1,0,
  -1,0,1,0,1,0,1,0,
  -1,0,1,0,1,0,-1,0,
  -1,0,1,0,-1,0,1,0,
  -1,0,1,0,-1,0,-1,0,
  -1,0,-1,0,1,0,1,0,
  -1,0,-1,0,1,0,-1,0,
  -1,0,-1,0,-1,0,1,0,
  -1,0,-1,0,-1,0,-1,0,
  2,0,0,0,0,0,0,0,
  -2,0,0,0,0,0,0,0,
  0,0,2,0,0,0,0,0,
  0,0,-2,0,0,0,0,0,
  0,0,0,0,2,0,0,0,
  0,0,0,0,-2,0,0,0,
  0,0,0,0,0,0,2,0,
  0,0,0,0,0,0,-2,0,
  0,0,1,0,-1,1,0,1,
  0,0,1,0,-1,1,0,-1,
  0,0,1,0,1,-1,0,1,
  0,0,1,0,1,-1,0,-1,
  0,0,-1,0,-1,1,0,1,
  0,0,-1,0,-1,1,0,-1,
  0,0,-1,0,1,-1,0,1,
  0,0,-1,0,1,-1,0,-1,
  0,0,0,1,1,0,-1,1,
  0,0,0,-1,1,0,-1,1,
  0,0,0,1,1,0,1,-1,
  0,0,0,-1,1,0,1,-1,
  0,0,0,1,-1,0,-1,1,
  0,0,0,-1,-1,0,-1,1,
  0,0,0,1,-1,0,1,-1,
  0,0,0,-1,-1,0,1,-1,
  0,0,-1,1,0,1,1,0,
  0,0,-1,1,0,-1,1,0,
  0,0,1,-1,0,1,1,0,
  0,0,1,-1,0,-1,1,0,
  0,0,-1,1,0,1,-1,0,
  0,0,-1,1,0,-1,-1,0,
  0,0,1,-1,0,1,-1,0,
  0,0,1,-1,0,-1,-1,0,
  1,0,0,0,0,1,-1,1,
  1,0,0,0,0,-1,-1,1,
  1,0,0,0,0,1,1,-1,
  1,0,0,0,0,-1,1,-1,
  -1,0,0,0,0,1,-1,1,
  -1,0,0,0,0,-1,-1,1,
  -1,0,0,0,0,1,1,-1,
  -1,0,0,0,0,-1,1,-1,
  -1,1,0,0,1,0,0,1,
  -1,1,0,0,1,0,0,-1,
  1,-1,0,0,1,0,0,1,
  1,-1,0,0,1,0,0,-1,
  -1,1,0,0,-1,0,0,1,
  -1,1,0,0,-1,0,0,-1,
  1,-1,0,0,-1,0,0,1,
  1,-1,0,0,-1,0,0,-1,
  0,1,0,0,-1,1,1,0,
  0,-1,0,0,-1,1,1,0,
  0,1,0,0,1,-1,1,0,
  0,-1,0,0,1,-1,1,0,
  0,1,0,0,-1,1,-1,0,
  0,-1,0,0,-1,1,-1,0,
  0,1,0,0,1,-1,-1,0,
  0,-1,0,0,1,-1,-1,0,
  1,0,-1,1,0,0,0,1,
  1,0,-1,1,0,0,0,-1,
  1,0,1,-1,0,0,0,1,
  1,0,1,-1,0,0,0,-1,
  -1,0,-1,1,0,0,0,1,
  -1,0,-1,1,0,0,0,-1,
  -1,0,1,-1,0,0,0,1,
  -1,0,1,-1,0,0,0,-1,
  0,1,1,0,0,0,-1,1,
  0,-1,1,0,0,0,-1,1,
  0,1,1,0,0,0,1,-1,
  0,-1,1,0,0,0,1,-1,
  0,1,-1,0,0,0,-1,1,
  0,-1,-1,0,0,0,-1,1,
  0,1,-1,0,0,0,1,-1,
  0,-1,-1,0,0,0,1,-1,
  -1,1,0,1,0,0,1,0,
  -1,1,0,-1,0,0,1,0,
  1,-1,0,1,0,0,1,0,
  1,-1,0,-1,0,0,1,0,
  -1,1,0,1,0,0,-1,0,
  -1,1,0,-1,0,0,-1,0,
  1,-1,0,1,0,0,-1,0,
  1,-1,0,-1,0,0,-1,0,
  1,0,0,1,-1,1,0,0,
  1,0,0,-1,-1,1,0,0,
  1,0,0,1,1,-1,0,0,
  1,0,0,-1,1,-1,0,0,
  -1,0,0,1,-1,1,0,0,
  -1,0,0,-1,-1,1,0,0,
  -1,0,0,1,1,-1,0,0,
  -1,0,0,-1,1,-1,0,0,
  -1,1,1,0,0,1,0,0,
  -1,1,1,0,0,-1,0,0,
  1,-1,1,0,0,1,0,0,
  1,-1,1,0,0,-1,0,0,
  -1,1,-1,0,0,1,0,0,
  -1,1,-1,0,0,-1,0,0,
  1,-1,-1,0,0,1,0,0,
  1,-1,-1,0,0,-1,0,0,
  0,1,-1,1,1,0,0,0,
  0,-1,-1,1,1,0,0,0,
  0,1,1,-1,1,0,0,0,
  0,-1,1,-1,1,0,0,0,
  0,1,-1,1,-1,0,0,0,
  0,-1,-1,1,-1,0,0,0,
  0,1,1,-1,-1,0,0,0,
  0,-1,1,-1,-1,0,0,0
]

/-- Reshape the flat integer table into quaternions, eight ints per vertex.
    Structural recursion on the tail `rest`, so it is kernel-reducible (no
    `partial`). -/
def chunk : List Int → List Quat
  | a0 :: b0 :: a1 :: b1 :: a2 :: b2 :: a3 :: b3 :: rest =>
      ⟨⟨a0, b0⟩, ⟨a1, b1⟩, ⟨a2, b2⟩, ⟨a3, b3⟩⟩ :: chunk rest
  | _ => []

/-- The 120 doubled icosians = vertices of the 600-cell (squared length 4). -/
def V : List Quat := chunk vflat

/-- The `±(p,q)` identification halves the proper- and improper-map counts. -/
def vpairs : List (Quat × Quat) := V.bind (fun p => V.map (fun q => (p, q)))

/-- Fast structural equality (avoids `Decidable`-instance overhead in `#eval`). -/
@[inline] def zbeq (x y : Ztau) : Bool := x.a == y.a && x.b == y.b
@[inline] def qbeq (a b : Quat) : Bool :=
  zbeq a.w b.w && zbeq a.x b.x && zbeq a.y b.y && zbeq a.z b.z

/-- Proper map `p·x·q̄` fixes `x` (in doubled coords: `p·x·q̄ = 4·x`). -/
@[inline] def fixesProper (p q x : Quat) : Bool :=
  qbeq (qmul (qmul p x) (qconj q)) (qscale 4 x)
/-- Improper map `p·x̄·q̄` fixes `x` (in doubled coords: `p·x̄·q̄ = 4·x`). -/
@[inline] def fixesImproper (p q x : Quat) : Bool :=
  qbeq (qmul (qmul p (qconj x)) (qconj q)) (qscale 4 x)

/-- `Sym x = |{ g ∈ W(H₄) : g•x = x }|`, by real enumeration over `V × V`. -/
def Sym (x : Quat) : Nat :=
  let np := (vpairs.filter (fun pq => fixesProper pq.1 pq.2 x)).length
  let ni := (vpairs.filter (fun pq => fixesImproper pq.1 pq.2 x)).length
  (np + ni) / 2

/-- `⌊log₃ p⌋` (largest `m` with `3^m ≤ p`), fuel-bounded for termination. -/
def ilog3 (p : Nat) : Nat :=
  let rec go (m acc fuel : Nat) : Nat :=
    match fuel with
    | 0 => m
    | fuel + 1 => if acc * 3 ≤ p then go (m + 1) (acc * 3) fuel else m
  go 0 1 (p + 1)

/-- Deterministic Module-A decode `p ↦ (q, m, k, r)` embedded as the ℤ[τ]⁴
    quaternion `v(p) = (q, m·τ, k, r·τ)`. -/
def decodeQuat (p : Nat) : Quat :=
  let m   : Nat := ilog3 p
  let pw  : Nat := 3 ^ m
  let q   : Nat := p / pw
  let r0  : Nat := (((q * pw : Nat) : Int) - (p : Int)).natAbs
  let k   : Nat := r0 / 143
  let r   : Nat := r0 - k * 143
  ⟨⟨(q : Int), 0⟩, ⟨0, (m : Int)⟩, ⟨(k : Int), 0⟩, ⟨0, (r : Int)⟩⟩

/-- `Sym` keyed by a natural number `p` through the deterministic decode. -/
def symOf (p : Nat) : Nat := Sym (decodeQuat p)

/-- The origin, fixed by every element of `W(H₄)`. -/
def origin : Quat := ⟨⟨0,0⟩, ⟨0,0⟩, ⟨0,0⟩, ⟨0,0⟩⟩

/-- Lagrange check: does each observed stabilizer order divide `|W(H₄)| = 14400`? -/
def symDvd? (p : Nat) : Bool := 14400 % symOf p == 0

end H4Strata
