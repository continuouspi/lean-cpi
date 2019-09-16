/-- An equivalency relationship over some type, based on a bidirectional
    chain of rewrite rules.
-/
inductive rule_equiv {α : Type} (rewrite : α → α → Type)
        : α → α → Prop
| refl {} {A : α} : rule_equiv A A
| forward  {A B C : α} : rewrite A B → rule_equiv B C → rule_equiv A C
| backward {A B C : α} : rewrite B A → rule_equiv B C → rule_equiv A C


infix ` ↣ `:51 := rule_equiv.forward
infix ` ↢ `:51 := rule_equiv.backward

namespace rule_equiv
  variables {α : Type}
  variables rule : α → α → Type

  local infix ` ~ `:51 := rule_equiv rule
  local infix ` ⟶ `:51 := rule

  -- Note, proofs are done using explicit induction rather than recursion, as it
  -- makes proving totality much easier.

  /-- Proving symmetry is effectively equivalent to reversing the linked list of
      rewrite rules. Thus we use the typical left fold, accumulating the
      reversed list. -/
  private def symm_worker {A B X : α} : A ~ X → A ~ B → B ~ X := begin
    intros prev this,
    induction this,
    case rule_equiv.refl { from prev },
    case rule_equiv.forward : A' B' C' eq next ih { from ih (eq ↢ prev) },
    case rule_equiv.backward : A' B' C' eq next ih { from ih (eq ↣ prev) }
  end

  protected theorem symm {A B : α} : A ~ B → B ~ A := symm_worker rule refl

  protected theorem trans {A B C : α} : A ~ B → B ~ C → A ~ C := begin
    intros this rest,
    induction this,
      case rule_equiv.refl { from rest },
      case rule_equiv.forward : A' B' C' eq next ih {
        from forward eq (ih rest)
      },
      case rule_equiv.backward : A' B' C' eq next ih {
        from backward eq (ih rest)
      }
  end


  -- variables α_subst  : ∀ {Γ Δ : context}, (name Γ → name Δ) → α Γ → α Δ
  -- variables rw_subst : ∀ {Γ Δ : context} {A B : α Γ} (ρ : name Γ → name Δ)
  --                    , A ⟶ B → α_subst ρ A ⟶ α_subst ρ B

  -- protected def subst {Γ Δ} (ρ : name Γ → name Δ) :
  --   ∀ {A B : α Γ}, A ~ B → α_subst ρ A ~ α_subst ρ B
  -- | ._ ._ refl := refl
  -- | ._ ._ (eq ↣ next) := rw_subst ρ eq ↣ subst next
  -- | ._ ._ (eq ↢ next) := rw_subst ρ eq ↢ subst next

  -- protected def wrap.subst {Γ Δ} (ρ : name Γ → name Δ) {A B : α Γ}
  --   : wrap rewrite A B → wrap rewrite (α_subst ρ A) (α_subst ρ B)
  --  | (wrap.intro eq) := wrap.intro (equiv.subst rewrite @α_subst @rw_subst ρ eq)

  /-- A wrapper for equivalency - as we cannot make equiv or rewrite Props, we
      need to wrap them to allow for a more convenient syntax.
    -/

  protected def is_equiv : is_equiv α (rule_equiv rule) :=
    { refl := λ A, refl,
      symm := λ A B , rule_equiv.symm rule,
      trans := λ A B C, rule_equiv.trans rule }

  protected def setoid : setoid α :=
    let eq := rule_equiv.is_equiv rule in
    ⟨ rule_equiv rule, ⟨ eq.refl, eq.symm, eq.trans ⟩ ⟩

end rule_equiv
