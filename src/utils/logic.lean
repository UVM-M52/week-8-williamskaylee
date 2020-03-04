
open classical
attribute [instance] classical.prop_decidable

namespace logic

lemma of_contrapositive {P Q : Prop} :
(¬ Q → ¬ P) → (P → Q) :=
begin
intros H hp,
by_cases hq : Q,
assumption,
apply absurd hp,
apply H,
assumption,
end

lemma of_cases {P Q : Prop} : (P → Q) → (¬ P → Q) → Q :=
begin
intros ht hf,
by_cases h : P,
apply ht,
assumption,
apply hf,
assumption,
end

lemma resolve_left {P Q : Prop} :
(¬ Q → P) → P ∨ Q :=
begin
intro H,
by_cases hq : Q,
right,
assumption,
left,
apply H,
assumption,
end

lemma double_negation {P : Prop} : P → ¬ ¬ P :=
begin
intros h f,
apply f,
assumption,
end

lemma resolve_right {P Q : Prop} :
(¬ P → Q) → P ∨ Q :=
begin
intro H,
by_cases hp : P,
left,
assumption,
right,
apply H,
assumption,
end

lemma demorgan_and {P Q : Prop} : ¬ P ∨ ¬ Q → ¬ (P ∧ Q) :=
begin
intros K h,
cases h with hp hq,
cases K,
apply K,
assumption,
apply K,
assumption,
end

lemma demorgan_exists {α : Sort*} {P : α → Prop} : (∀ x, ¬ P x) → ¬ (∃ x, P x) :=
begin
intros K h,
cases h with x hx,
apply K x,
assumption,
end

lemma demorgan_forall {α : Sort*} {P : α → Prop} : (∃ x, ¬ P x) → ¬ (∀ x, P x) :=
begin
intros K h,
cases K with x kx,
apply kx,
apply h,
end

lemma demorgan_or {P Q : Prop} : ¬ P ∧ ¬ Q → ¬ (P ∨ Q) :=
begin
intros K h,
cases K with Kp Kq,
cases h,
apply Kp,
assumption,
apply Kq,
assumption,
end

lemma demorgan_and' {P Q : Prop} : ¬ (P ∧ Q) → ¬ P ∨ ¬ Q :=
begin
intro H,
by_cases hp : P,
by_cases hq : Q,
apply absurd _ H,
split; assumption,
right, assumption,
left, assumption,
end

lemma demorgan_or' {P Q : Prop} : ¬ (P ∨ Q) → ¬ P ∧ ¬ Q :=
begin
intro H,
by_cases hp : P,
apply absurd _ H,
left, assumption,
by_cases hq : Q,
apply absurd _ H,
right, assumption,
split,
assumption,
assumption,
end

lemma demorgan_exists' {α : Sort*} {P : α → Prop} : ¬ (∃ x, P x) → (∀ x, ¬ P x) :=
begin
intros H x hx,
apply H,
existsi x,
assumption,
end

lemma demorgan_forall' {α : Sort*} {P : α → Prop} : ¬ (∀ x, P x) → (∃ x, ¬ P x) :=
begin
intros H,
by_cases H' : ∃ x, ¬ P x,
assumption,
apply absurd _ H,
intro x,
by_cases P x,
assumption,
apply absurd _ H',
existsi x,
assumption,
end

end logic

namespace tactic

meta def interactive.resolve_left : tactic unit := `[apply logic.resolve_left]

meta def interactive.resolve_right : tactic unit := `[apply logic.resolve_right]

meta def interactive.by_contrapositive : tactic unit :=
`[apply logic.of_contrapositive]

meta def interactive.by_demorgan : tactic unit :=
`[ apply logic.double_negation
  <|> apply logic.demorgan_and
  <|> apply logic.demorgan_or
  <|> apply logic.demorgan_exists
  <|> apply logic.demorgan_forall]

--meta def interactive.by_demorgan : tactic unit :=


end tactic