Theorem frobenius (A : Set) (p : A -> Prop) (q : Prop) : 
  (exists x : A, q /\ p x) <-> (q /\ exists x : A, p x).
Proof.
  split.
  intros.
  destruct H as [x [H1 H2]].
  split.
  assumption.
  exists x.
  assumption.
  intros [H1 [x H2]].
  exists x.
  split.
  assumption.
  assumption.
Qed.

Theorem hilbert_axiom_S (P Q R : Prop) : (P -> Q -> R) -> (P -> Q) -> P -> R.
Proof.
  intros.
  pose (P_implies_Q := H0 H1).
  pose (P_and_Q_implies_R := H H1 P_implies_Q).
  exact P_and_Q_implies_R.
Qed.

Inductive or (A B : Prop) : Prop :=
  | or_introl : A -> A \/ B
  | or_intror : B -> A \/ B
where "A \/ B" := (or A B) : type_scope.

(* Try to Prove Demorgan's Law -- Stuck trying to prove P *)
Theorem demorgans_law (P Q : Prop) :
 (~(P \/ Q) <-> (~P /\ ~Q)).
Proof.
  split.
  split.
  intros P'.
  apply H.
  left.
  assumption.
  intros Q'.
  apply H.
  right.
  assumption.
  intro H.
  destruct H as [P' Q'].
  absurd P.
  assumption.
  pose (disj_P := or_introl (P) (P)).
Qed.

(* Attempting to Prove this Tautology -- Stuck trying to prove R *)
Theorem tautology1 : (forall P Q R : Prop, 
  (P /\ (Q \/ R)) -> ((P /\ Q) \/ (P /\ R))).
Proof.
  intros P Q R.
  intros left_side.
  right.
  elim left_side.
  split.
  apply left_side.
  destruct left_side.
Qed.