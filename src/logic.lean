section propositional

variables P Q R : Prop


------------------------------------------------
-- Proposições de dupla negaço:
------------------------------------------------

theorem doubleneg_intro :
  P → ¬¬P  :=
begin
  intros hp hpf, --"Suponha P, ¬P"
  have hf : false := hpf hp, --"Como P → ⊥ e P, logo ⊥"
  exact hf, --"Imediato (tenho meu alvo nos meus dados)"
end

theorem doubleneg_elim :
  ¬¬P → P  :=
begin
  intro hpf,
  by_cases p : P,
  exact p,
  exfalso,
  have hboom : false := hpf p,
  exact hboom,
end

theorem doubleneg_law :
  ¬¬P ↔ P  :=
begin
  split,
  apply doubleneg_elim,
  apply doubleneg_intro,
end

------------------------------------------------
-- Comutatividade dos ∨,∧:
------------------------------------------------

theorem disj_comm :
  (P ∨ Q) → (Q ∨ P)  :=
begin
  intro poq,
  cases poq with hp hq,
  right,
  exact hp,
  left,
  exact hq,
end

theorem conj_comm :
  (P ∧ Q) → (Q ∧ P)  :=
begin
  intro peq,
  cases peq with hp hq,
  split,
  exact hq,
  exact hp,
end


------------------------------------------------
-- Proposições de interdefinabilidade dos →,∨:
------------------------------------------------

theorem impl_as_disj_converse :
  (¬P ∨ Q) → (P → Q)  :=
begin
  intro h_fp_or_q,
  intro p,
  cases h_fp_or_q with hp hq,
  exfalso,
  contradiction,
  exact hq,
end

theorem disj_as_impl :
  (P ∨ Q) → (¬P → Q)  :=
begin
  intro h,
  intro np,
  cases h with hp hq,
  exfalso,
  contradiction,
  exact hq,
end


------------------------------------------------
-- Proposições de contraposição:
------------------------------------------------

theorem impl_as_contrapositive :
  (P → Q) → (¬Q → ¬P)  :=
begin
  intros hpq hnq hp,
  have hq := hpq hp,
  contradiction,
end

theorem impl_as_contrapositive_converse :
  (¬Q → ¬P) → (P → Q)  :=
begin
  intros hnq_np p,
  by_cases hq : Q,
  exact hq,
  exfalso,
  have hnp := hnq_np hq,
  have hboom := hnp p,
  contradiction,
end

theorem contrapositive_law :
  (P → Q) ↔ (¬Q → ¬P)  :=
begin
  split,
  apply impl_as_contrapositive,
  apply impl_as_contrapositive_converse,
end


------------------------------------------------
-- A irrefutabilidade do LEM:
------------------------------------------------

theorem lem_irrefutable :
  ¬¬(P∨¬P)  :=
begin
  intro n_p_np,
  apply n_p_np,
  right,
  intro p,
  have p_or_q : P ∨ ¬P,
  left,
  exact p,
  contradiction,
end


------------------------------------------------
-- A lei de Peirce
------------------------------------------------

theorem peirce_law_weak :
  ((P → Q) → P) → ¬¬P  :=
begin
  intros pq_p np,
  have p : P,
  apply pq_p,
  intro p,
  exfalso,
  contradiction,
  contradiction,
end


------------------------------------------------
-- Proposições de interdefinabilidade dos ∨,∧:
------------------------------------------------

theorem disj_as_negconj :
  P∨Q → ¬(¬P∧¬Q)  :=
begin
  intro poq,
  intro np_nq,
  cases np_nq with np nq,
  cases poq,
  contradiction,
  contradiction,
end

theorem conj_as_negdisj :
  P∧Q → ¬(¬P∨¬Q)  :=
begin
  intro p_and_q,
  intro np_or_nq,
  cases p_and_q with p q,
  cases np_or_nq,
  contradiction,
  contradiction,
end


------------------------------------------------
-- As leis de De Morgan para ∨,∧:
------------------------------------------------

theorem demorgan_ndisj :
  ¬(P∨Q) → (¬P ∧ ¬Q)  :=
begin
  intro n_p_or_q,
  split,
  intro p,
  have p_or_q : P ∨ Q,
  left,
  exact p,
  contradiction,
  intro q,
  have p_or_q : P ∨ Q,
  right,
  exact q,
  contradiction,
end

theorem demorgan_ndisj_converse :
  (¬P ∧ ¬Q) → ¬(P∨Q)  :=
begin
  intros np_and_nq p_or_q,
  cases np_and_nq with np nq,
  cases p_or_q,
  contradiction,
  contradiction,
end

theorem demorgan_nconj_converse :
  (¬Q ∨ ¬P) → ¬(P∧Q)  :=
begin
  intros nq_or_np p_and_q,
  cases p_and_q with p q,
  cases nq_or_np,
  contradiction,
  contradiction,
end


------------------------------------------------
-- Proposições de distributividade dos ∨,∧:
------------------------------------------------

theorem distr_conj_disj :
  P∧(Q∨R) → (P∧Q)∨(P∧R)  :=
begin
  intro p_and_pr,
  cases p_and_pr with p q_and_r,
  cases q_and_r with q r,
  left,
  split,
  repeat {assumption},
  right,
  split,
  repeat {assumption},
end

theorem distr_conj_disj_converse :
  (P∧Q)∨(P∧R) → P∧(Q∨R)  :=
begin
  intro pq_or_pr,
  cases pq_or_pr with pq pr,
  cases pq with p q,
  split,
  exact p,
  left,
  exact q,
  split,
  cases pr with p r,
  exact p,
  right,
  cases pr with p r,
  exact r,
end

theorem distr_disj_conj :
  P∨(Q∧R) → (P∨Q)∧(P∨R)  :=
begin
  intro p_or_qandr,
  cases p_or_qandr with p qandr,
  split,
  left,
  exact p,
  left,
  exact p,
  cases qandr with q r,
  split,
  right,
  exact q,
  right,
  exact r,
end

theorem distr_disj_conj_converse :
  (P∨Q)∧(P∨R) → P∨(Q∧R)  :=
begin
  intro porq_and_porr,
  cases porq_and_porr with p_or_q p_or_r,
  cases p_or_r with p r,
  left,
  exact p,
  cases p_or_q with p q,
  left,
  exact p,
  right,
  split,
  exact q,
  exact r,
end


------------------------------------------------
-- Currificação
------------------------------------------------

theorem curry_prop :
  ((P∧Q)→R) → (P→(Q→R))  :=
begin
  intros pandq_imp_r p q,
  apply pandq_imp_r,
  split,
  repeat {assumption},
end

theorem uncurry_prop :
  (P→(Q→R)) → ((P∧Q)→R)  :=
begin
  intros p_q_r p_and_q,
  apply p_q_r,
  cases p_and_q with p q,
  exact p,
  cases p_and_q with p q,
  exact q,
end


------------------------------------------------
-- Reflexividade da →:
------------------------------------------------

theorem impl_refl :
  P → P  :=
begin
  intro p,
  exact p,
end

------------------------------------------------
-- Weakening and contraction:
------------------------------------------------

theorem weaken_disj_right :
  P → (P∨Q)  :=
begin
  intro p,
  left,
  exact p,
end

theorem weaken_disj_left :
  Q → (P∨Q)  :=
begin
  intro q,
  right,
  exact q,
end

theorem weaken_conj_right :
  (P∧Q) → P  :=
begin
  intro p_and_q,
  cases p_and_q with p q,
  exact p,
end

theorem weaken_conj_left :
  (P∧Q) → Q  :=
begin
  intro p_and_q,
  cases p_and_q with p q,
  exact q,
end

theorem conj_idempot :
  (P∧P) ↔ P :=
begin
  split,
  intro p_and_p,
  cases p_and_p with p p,
  exact p,
  intro p,
  split,
  repeat {exact p},
end

theorem disj_idemp :
  (P∨P) ↔ P  :=
begin
  split,
  intro p_or_p,
  cases p_or_p with p p,
  repeat {exact p},
  intro p,
  left,
  exact p,
end

end propositional


----------------------------------------------------------------


section predicate

variable U : Type
variables P Q : U -> Prop


------------------------------------------------
-- As leis de De Morgan para ∃,∀:
------------------------------------------------

theorem demorgan_exists_neg :
  (∃x, ¬P x) → ¬(∀x, P x)  :=
begin
  intro h,
  cases h with x npx,
  intro all_p,
  have px := all_p x,
  contradiction,
end

theorem demorgan_neg_exists :
  ¬(∃x, P x) → (∀x, ¬P x)  :=
begin
  intros ex_px u pu,
  apply ex_px,
  existsi u,
  exact pu,
end

theorem demorgan_forall_neg :
  (∀x, ¬P x) → ¬(∃x, P x)  :=
begin
  intros all_npx ex_px,
  cases ex_px with u p_u,
  have np_u := all_npx u,
  contradiction,
end

theorem demorgan_neg_forall :
  ¬(∀x, P x) → (∃x, ¬P x)  :=
begin
  intro n_all_p,
  exfalso,
  apply n_all_p,
  intro u,
  by_cases npu : P u,
  exact npu,

end

theorem demorgan_exists_law :
  (∃x, ¬P x) ↔ ¬(∀x, P x)  :=
begin
  split,
  apply demorgan_exists_neg,
  apply demorgan_neg_forall,
end

theorem demorgan_forall_law :
  (∀x, ¬P x) ↔ ¬(∃x, P x)  :=
begin
  split,
  apply demorgan_forall_neg,
  apply demorgan_neg_exists,
end


------------------------------------------------
-- Proposições de interdefinabilidade dos ∃,∀:
------------------------------------------------

theorem exists_as_neg_forall :
  (∃x, P x) → ¬(∀x, ¬P x)  :=
begin
  intros ex_p all_np,
  cases ex_p with u pu,
  have npu := all_np u,
  contradiction,
end

theorem forall_as_neg_exists :
  (∀x, P x) → ¬(∃x, ¬P x)  :=
begin
  intros all_p ex_np,
  cases ex_np with u npu,
  have pu := all_p u,
  contradiction,
end

theorem forall_as_neg_exists_converse :
  ¬(∃x, ¬P x) → (∀x, P x)  :=
begin
  intro n_ex_np,
  intro u,
  exfalso,
  apply n_ex_np,
  existsi u,
  intro pu,

  sorry,
  --work in progress
end

theorem exists_as_neg_forall_converse :
  ¬(∀x, ¬P x) → (∃x, P x)  :=
begin
  intro n_all_np,
  
end

theorem forall_as_neg_exists_law :
  (∀x, P x) ↔ ¬(∃x, ¬P x)  :=
begin
  split,
  apply forall_as_neg_exists,
  apply forall_as_neg_exists_converse,
end

theorem exists_as_neg_forall_law :
  (∃x, P x) ↔ ¬(∀x, ¬P x)  :=
begin
  split,
  apply exists_as_neg_forall,
  apply exists_as_neg_forall_converse,
end


------------------------------------------------
--  Proposições de distributividade de quantificadores:
------------------------------------------------

theorem exists_conj_as_conj_exists :
  (∃x, P x ∧ Q x) → (∃x, P x) ∧ (∃x, Q x)  :=
begin
  intro ex_p_and_q,
  cases ex_p_and_q with u pu_and_qu,
  cases pu_and_qu with pu qu,
  split,
  existsi u,
  assumption,
  existsi u,
  assumption,
end

theorem exists_disj_as_disj_exists :
  (∃x, P x ∨ Q x) → (∃x, P x) ∨ (∃x, Q x)  :=
begin
  intro ex_p_or_q,
  cases ex_p_or_q with u pu_or_qu,
  cases pu_or_qu with pu pq,
  left,
  existsi u,
  assumption,
  right,
  existsi u,
  assumption,
end

theorem exists_disj_as_disj_exists_converse :
  (∃x, P x) ∨ (∃x, Q x) → (∃x, P x ∨ Q x)  :=
begin
  intro exp_or_exq,
  cases exp_or_exq with exp exq,
  cases exp with u pu,
  existsi u,
  left,
  assumption,
  cases exq with u qu,
  existsi u,
  right,
  assumption,
end

theorem forall_conj_as_conj_forall :
  (∀x, P x ∧ Q x) → (∀x, P x) ∧ (∀x, Q x)  :=
begin
  intro all_p_and_q,
  split,
  intro u,
  have pu_and_qu := all_p_and_q u,
  cases pu_and_qu with pu qu,
  assumption,
  intro x,
  have px_and_qx := all_p_and_q x,
  cases px_and_qx with px qx,
  assumption,
end

theorem forall_conj_as_conj_forall_converse :
  (∀x, P x) ∧ (∀x, Q x) → (∀x, P x ∧ Q x)  :=
begin
  intro allp_and_allq,
  intro a,
  cases allp_and_allq with all_p all_q,
  split,
  have pa := all_p a,
  assumption,
  have qa := all_q a,
  assumption,
end


theorem forall_disj_as_disj_forall_converse :
  (∀x, P x) ∨ (∀x, Q x) → (∀x, P x ∨ Q x)  :=
begin
  intro allp_or_allq,
  intro u,
  cases allp_or_allq with allp allq,
  have pu := allp u,
  left,
  assumption,
  have qu := allq u,
  right,
  assumption,
end


/- NOT THEOREMS --------------------------------

theorem forall_disj_as_disj_forall :
  (∀x, P x ∨ Q x) → (∀x, P x) ∨ (∀x, Q x)  :=
begin
  sorry,
end

theorem exists_conj_as_conj_exists_converse :
  (∃x, P x) ∧ (∃x, Q x) → (∃x, P x ∧ Q x)  :=
begin
  sorry,
end

---------------------------------------------- -/

end predicate
