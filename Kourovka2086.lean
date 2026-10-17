import Mathlib

/-!
# Kourovka Notebook problem 20.86 (P. Schmid): the finite part of the counterexample

Problem 20.86 asks: for a finite group `G` and a prime `p` with `s_p(G) = 1 + k p > 1` Sylow
`p`-subgroups and `|G_p| = |P| (1 + ℓ (p - 1))` `p`-elements, is always `ℓ^p ≥ k^(p-1)`?

`README.md` (which also contains the AI disclosure: this file was written by Claude, an AI model
made by Anthropic) answers **no** with
`p = 7`, `G = 𝔽₈⁷ ⋊ E`, `E = 7^{1+2}_+ ≤ GL₇(𝔽₈)`, where
`s_7(G) = 2^21`, `|G_7| = 1 + 6·8^7 + 336·8^6`, `k = 299593`, `ℓ = 48913`, `ℓ^7 < k^6`.

This file formalises the parts that are pure arithmetic or finite computation:

* `E`: the group of triples `(a, b, c) ∈ (ℤ/7)³` with product
  `(a, b, c) (a', b', c') = (a + a', b + b', c + c' - b a')`.  This is the standard form
  `g(a, b, c) = ω^c x^a y^b` of README.md, Section 3.2 (`y^b x^{a'} = ω^{-a'b} x^{a'} y^b`).
  We prove it is a group of order 343 and exponent 7 (`card_E`, `pow_seven`), that `x y = z y x`
  with `z = (0, 0, 1)` central (`comm_xy`), and that its centre is exactly `{(0, 0, c)}`
  (`center_iff`).  Together with `pow_seven` this is the statement "`E` is extraspecial of order
  `7^3` and exponent `7`", i.e. `7^{1+2}_+`.
* the counting identities and the final inequality (`sylow_count`, `p_elements`, `f_param`,
  `l_closed_form`, `main_inequality`, `gheri_inequality`) and the algebraic identity behind the
  closed form of `ℓ` for the whole family (`family_identity`).

Not formalised here: the faithful action of `E` on `𝔽₈⁷`, the fibre
count `|ker N_a|`, and the identification of `s_7(G)` and `|G_7|` with the numbers above.

No `native_decide`, no `sorry`; `#print axioms` lists only the standard axioms.
-/

namespace Kourovka2086

/-- The extraspecial group `7^{1+2}_+` in the standard form `g(a, b, c) = ω^c x^a y^b`. -/
@[ext] structure E where
  a : ZMod 7
  b : ZMod 7
  c : ZMod 7
deriving DecidableEq, Fintype

namespace E

/-- `g(a,b,c) g(a',b',c') = g(a + a', b + b', c + c' - b a')`. -/
def mul (g h : E) : E := ⟨g.a + h.a, g.b + h.b, g.c + h.c - g.b * h.a⟩

def one : E := ⟨0, 0, 0⟩

def inv (g : E) : E := ⟨-g.a, -g.b, -g.c - g.a * g.b⟩

instance : Mul E := ⟨mul⟩
instance : One E := ⟨one⟩
instance : Inv E := ⟨inv⟩

@[simp] lemma mul_a (g h : E) : (g * h).a = g.a + h.a := rfl
@[simp] lemma mul_b (g h : E) : (g * h).b = g.b + h.b := rfl
@[simp] lemma mul_c (g h : E) : (g * h).c = g.c + h.c - g.b * h.a := rfl
@[simp] lemma one_a : (1 : E).a = 0 := rfl
@[simp] lemma one_b : (1 : E).b = 0 := rfl
@[simp] lemma one_c : (1 : E).c = 0 := rfl
@[simp] lemma inv_a (g : E) : g⁻¹.a = -g.a := rfl
@[simp] lemma inv_b (g : E) : g⁻¹.b = -g.b := rfl
@[simp] lemma inv_c (g : E) : g⁻¹.c = -g.c - g.a * g.b := rfl

instance : Group E where
  mul_assoc x y z := by ext <;> simp <;> ring
  one_mul x := by ext <;> simp
  mul_one x := by ext <;> simp
  inv_mul_cancel x := by ext <;> simp <;> ring

/-- `x = diag(1, ω, …, ω⁶)` in the standard form. -/
def x : E := ⟨1, 0, 0⟩
/-- `y` = the cyclic permutation matrix. -/
def y : E := ⟨0, 1, 0⟩
/-- `z = ω I`, the scalar matrix. -/
def z : E := ⟨0, 0, 1⟩

/-- `|E| = 343`. -/
theorem card_E : Fintype.card E = 343 := by decide +kernel

/-- `E` has exponent 7. -/
theorem pow_seven : ∀ g : E, g ^ 7 = 1 := by decide +kernel

/-- `x y = z (y x)`, i.e. `x y x⁻¹ y⁻¹ = ω I`. -/
theorem comm_xy : x * y = z * (y * x) := by decide +kernel

/-- `z` is central. -/
theorem z_central : ∀ g : E, z * g = g * z := by decide +kernel

/-- The centre of `E` is exactly `{(0, 0, c)}` (the seven scalar matrices). -/
theorem center_iff (g : E) : (∀ h : E, g * h = h * g) ↔ (g.a = 0 ∧ g.b = 0) := by
  constructor
  · intro H
    have hx := congrArg E.c (H x)
    have hy := congrArg E.c (H y).symm
    simp [x, y] at hx hy
    exact ⟨hy, hx⟩
  · rintro ⟨ha, hb⟩ h
    ext <;> simp [ha, hb, add_comm]

/-- Every commutator is central and the commutator of `x, y` generates the centre:
`E' = Z(E)`, so `E` is extraspecial (with `pow_seven`: of exponent 7). -/
theorem commutator_central : ∀ g h : E, (g * h * g⁻¹ * h⁻¹).a = 0 ∧ (g * h * g⁻¹ * h⁻¹).b = 0 := by
  intro g h
  constructor <;> simp

end E

/-! ## The numbers -/

/-- `s_7(G) = 2^21 = 1 + 7 k` with `k = 299593`. -/
theorem sylow_count : (2 : ℕ) ^ 21 = 1 + 7 * 299593 := by norm_num

/-- `|G_7| = 1 + 6·8^7 + 336·8^6 = 343 · f` with `f = 293479`. -/
theorem p_elements : 1 + 6 * 8 ^ 7 + 336 * 8 ^ 6 = (343 : ℕ) * 293479 := by norm_num

/-- `f = 1 + 6 ℓ` with `ℓ = 48913`. -/
theorem f_param : (293479 : ℕ) = 1 + 6 * 48913 := by norm_num

/-- closed form `ℓ = (8^8 - 57) / 7^3`. -/
theorem l_closed_form : (8 : ℕ) ^ 8 - 57 = 343 * 48913 := by norm_num

/-- **The answer to 20.86 is no**: `ℓ^7 < k^6`. -/
theorem main_inequality : (48913 : ℕ) ^ 7 < 299593 ^ 6 := by norm_num

/-- Gheri's inequality `f^7 ≥ s^6` does hold for this (solvable) group. -/
theorem gheri_inequality : (2 : ℕ) ^ 126 ≤ 293479 ^ 7 := by norm_num

/-- The algebraic identity behind the family formula: with `A = Q^p`, `B = Q^(p-1)`,
`|G_p| - p^3 = 1 + (p-1) A + (p^3 - p) B - p^3 = (p - 1) (A + p (p+1) B - (p^2 + p + 1))`,
so `ℓ = (A + p (p+1) B - (p^2+p+1)) / p^3`. -/
theorem family_identity (p A B : ℤ) :
    1 + (p - 1) * A + (p ^ 3 - p) * B - p ^ 3 = (p - 1) * (A + p * (p + 1) * B - (p ^ 2 + p + 1)) := by
  ring

end Kourovka2086

#print axioms Kourovka2086.E.card_E
#print axioms Kourovka2086.E.pow_seven
#print axioms Kourovka2086.E.center_iff
#print axioms Kourovka2086.main_inequality
