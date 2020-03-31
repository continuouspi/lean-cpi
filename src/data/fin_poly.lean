import data.fin_fn

/-- A multi-variate, computable polynomial. Based off mathlib's mv_polynomial
    definition. -/
def fin_poly (α : Type*) (β : Type*) [has_zero β] := fin_fn (fin_fn α ℕ) β

section instances
  variables (α : Type*) (β : Type*)

  instance [has_zero β] [decidable_eq α] [decidable_eq β] : decidable_eq (fin_poly α β) := fin_fn.decidable_eq _ β
  instance [comm_ring β] [decidable_eq α] [decidable_eq β] : comm_ring (fin_poly α β) := fin_fn.comm_ring _ β
  instance [half_ring β] [decidable_eq α] [decidable_eq β] : half_ring (fin_poly α β) := fin_fn.half_ring _ β

  instance [has_zero β] [has_repr α] [has_repr β] : has_repr (fin_poly α β) :=
    let show_var (x : α) (n : ℕ) := if n = 1 then repr x else repr x ++ "^" ++ repr n in
    let show_single (x : fin_fn α ℕ) (c : β) :=
      if x.support.card = 0 then repr c else repr c ++ "•" ++ "("
      ++ string.intercalate "•" ((x.support.val.map (λ a, show_var a (x.space a))).sort (≤))
      ++ ")"
    in
    ⟨ λ x, "(" ++ string.intercalate " + " ((x.support.val.map (λ a, show_single a (x.space a))).sort (≤)) ++ ")" ⟩

  instance [has_zero β] : inhabited (fin_poly α β) := fin_fn.inhabited _ β
end instances

namespace fin_poly
variables {α : Type*} {β : Type*} [decidable_eq α] [decidable_eq β]

/-- A constant polynomial. -/
def C [has_zero β] (c : β) : fin_poly α β := fin_fn.single 0 c

/-- A distributive embedding of some ring into polynomials of that ring. -/
def C.embed {σ : Type*} {α : Type*} [decidable_eq σ] [decidable_eq α] [comm_semiring α] : α ↪ fin_poly σ α
:= { to_fun := C, inj := fin_fn.single.inj _ }

/-- A "variable" `x` of degree 1.  -/
def X [ring β] (x : α) : fin_poly α β := fin_fn.single (fin_fn.single x 1) 1

end fin_poly

#lint-
