import tactic.lint

variables {α : Type*}

/-- A property which determins whether this option is inhabited. -/
def option.is_some' : option α → Prop
| (some _) := true
| none := false

instance option.is_some'.decide : decidable_pred (@option.is_some' α)
| (some _) := decidable.true
| none := decidable.false

/-- Extract the value of an option, given a proof it exists. -/
def option.get' : ∀ {o : option α}, option.is_some' o → α
| (some k) _ := k

lemma option.eq_some_of_is_some' : ∀ {o : option α} (h : option.is_some' o), o = some (option.get' h)
| (some x) _ := rfl

#lint-
