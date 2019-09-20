import data.cpi.concretion.basic

run_cmd sanity_check
set_option profiler true
set_option profiler.threshold 0.5

namespace cpi
namespace concretion

inductive equiv : ∀ {Γ} {b y}, concretion Γ b y → concretion Γ b y → Prop
| refl  {Γ} {b y} {F : concretion Γ b y} : equiv F F
| trans {Γ} {b y} {F G H : concretion Γ b y} : equiv F G → equiv G H → equiv F H
| symm  {Γ} {b y} {F G : concretion Γ b y} : equiv F G → equiv G F

| ξ_parallel₁
    {Γ} {b y} {F F' : concretion Γ b y} {A : species Γ}
  : equiv F F' → equiv (F |₁ A) (F' |₁ A)
| ξ_parallel₂
    {Γ} {b y} {F F' : concretion Γ b y} {A : species Γ}
  : equiv F F' → equiv (F |₁ A) (F' |₁ A)
| ξ_restriction
    {Γ} {b y} (M : affinity) {F F' : concretion (context.extend M.arity Γ) b y}
  : equiv F F' → equiv (ν'(M) F) (ν'(M) F')

-- Parallel is a commutative monoid
| parallel_nil
    {Γ} {b y} {F : concretion Γ b y}
  : equiv (F |₁ species.nil) F
| parallel_symm
    {Γ} {b y} {F : concretion Γ b y} {A : species Γ}
  : equiv (F |₁ A) (A |₂ F)
| parallel_assoc₁
    {Γ} {b y} {F : concretion Γ b y} {A B : species Γ}
  : equiv ((F |₁ A) |₁ B) (F |₁ (A |ₛ B))
| parallel_assoc₂
    {Γ} {b y} {F : concretion Γ b y} {A B : species Γ}
  : equiv ((A |₂ F) |₁ B) (A |₂ (F |₁ B))

-- Projections for species into parallel/apply
| ξ_parallel
    {Γ} {b y} {F : concretion Γ b y} {A A' : species Γ}
  : A ≈ A' → equiv (F |₁ A) (F |₁ A')
| ξ_apply
    {Γ} {b y} {bs : vector (name Γ) b} {A A' : species (context.extend y Γ)}
  : A ≈ A' → equiv (#(bs; y) A) (#(bs; y) A')

-- Standard ν rules
| ν_parallel₁
    {Γ} {b y} (M : affinity)
    {A : species Γ} {F : concretion (context.extend M.arity Γ) b y}
  : equiv (ν'(M)(species.rename name.extend A |₂ F)) (A |₂ ν'(M) F)
| ν_parallel₂
    {Γ} {b y} (M : affinity)
    {A : species Γ} {F : concretion (context.extend M.arity Γ) b y}
  : equiv (ν'(M)(F |₁ species.rename name.extend A)) ((ν'(M) F) |₁ A)
| ν_drop
    {Γ} {b y} (M : affinity) {F : concretion Γ b y}
  : equiv (ν'(M) rename name.extend F) F
| ν_swap
    {Γ} {b y} (M N : affinity)
    {F : concretion (context.extend N.arity (context.extend M.arity Γ)) b y}
  : equiv (ν'(M)ν'(N) F) (ν'(N)ν'(M) rename name.swap F)

| apply_parallel
    {Γ} {b y} {bs : vector (name Γ) b}
    {A : species Γ} {B : species (context.extend y Γ)}
  : equiv (#(bs; y) (species.rename name.extend A |ₛ B)) (A |₂ #(bs; y) B)

instance {Γ} {b y} : is_equiv (concretion Γ b y) equiv :=
  { refl := @equiv.refl Γ b y, symm := @equiv.symm Γ b y, trans := @equiv.trans Γ b y }
instance {Γ} {b y} : is_refl (concretion Γ b y) equiv := ⟨ λ _, equiv.refl ⟩
instance {Γ} {b y} : setoid (concretion Γ b y) :=
  ⟨ equiv, ⟨ @equiv.refl Γ b y, @equiv.symm Γ b y, @equiv.trans Γ b y ⟩ ⟩
instance setoid.is_equiv {Γ} {b y} : is_equiv (concretion Γ b y) has_equiv.equiv :=
  concretion.is_equiv

end concretion
end cpi

#sanity_check
