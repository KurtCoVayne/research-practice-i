Require Import List.
Import ListNotations.
Require Import Arith.
Require Import Lia.
From Coq Require Import Wellfounded.
Require Import Coq.Relations.Relation_Definitions.

Inductive RoseTree : Type :=
  | Node : nat -> list RoseTree -> RoseTree.

(* Helper function to merge two lists of counts *)
Fixpoint merge_counts (l1 l2 : list nat) : list nat :=
  match l1, l2 with
  | [], l => l
  | l, [] => l
  | x1 :: xs1, x2 :: xs2 => (x1 + x2) :: merge_counts xs1 xs2
  end.

(* Function to count the number of elements at each level *)
Fixpoint _count_levels (t : RoseTree) : list nat :=
  match t with
  | Node _ children =>
      let child_counts := map _count_levels children in
      let merged := fold_left merge_counts child_counts [] in
      1 :: merged
  end.

(* Count levels is _count_levels but reversed to match the expected order *)
Definition count_levels (t : RoseTree) : list nat := rev (_count_levels t).

(* Example usage of count_levels *)

(* Example tree for testing *)

Definition example_tree : RoseTree :=
  Node 1 [ Node 2 []; Node 3 [ Node 4 []; Node 5 [] ] ].

Eval compute in count_levels example_tree.

Inductive step_internal (n : nat) : list nat -> list nat -> Prop :=
| StepInternalLong :
    forall prefix x y suffix,
      x > 0 ->
      length suffix >= 1 ->
      step_internal n (prefix ++ x :: y :: suffix)
                         (prefix ++ (x - 1) :: (y + n) :: suffix)
| StepInternalTwo :
    forall prefix x y,
      x > 0 ->
      step_internal n (prefix ++ x :: [y])
                         (prefix ++ (x - 1) :: [y]).

Inductive step_final : list nat -> list nat -> Prop :=
| StepFinal :
    forall prefix x,
      x > 0 ->
      step_final (prefix ++ [x]) (prefix ++ [x - 1]).

Inductive step_done : list nat -> Prop :=
| StepDoneEmpty :
    step_done []
| StepDoneNonEmpty :
    forall l,
      l <> [] ->
      (forall x, In x l -> x = 0) ->
      step_done l.

Inductive step (n : nat) : list nat -> list nat -> Prop :=
| Step_internal_case :
    forall l1 l2,
      step_internal n l1 l2 ->
      step n l1 l2
| Step_final_case :
    forall l1 l2,
      step_final l1 l2 ->
      step n l1 l2.

Inductive step_or_done (n : nat) : list nat -> list nat -> Prop :=
| Step_case :
    forall l1 l2,
      step n l1 l2 ->
      step_or_done n l1 l2
| Done_case :
    forall l,
      step_done l ->
      step_or_done n l l.

Eval compute in
  step_or_done 2 [1; 3] [0; 5].

(* Example usage of step_done *)

Example test_step_done_empty : step_done [].
Proof.
  apply StepDoneEmpty.
Qed.

Example test_step_done_zeros : step_done [0; 0; 0].
Proof.
  apply StepDoneNonEmpty.
  - discriminate. (* [0;0;0] <> [] *)
  - intros x H.
    destruct H as [H | [H | [H | []]]]; subst; auto.
Qed.

Lemma step_internal_preserves_length : 
  forall n l1 l2,
    step_internal n l1 l2 -> length l1 = length l2.
Proof.
  intros n l1 l2 H.
  inversion H; subst.
  - (* StepInternalLong *)
    repeat rewrite length_app.
    simpl. reflexivity.
  - (* StepInternalTwo *)
    repeat rewrite length_app.
    simpl. reflexivity.
Qed.

Lemma step_final_preserves_length : 
  forall l1 l2,
    step_final l1 l2 -> length l1 = length l2.
Proof.
  intros l1 l2 H.
  inversion H; subst.
  (* H : step_final (prefix ++ [x]) (prefix ++ [x - 1]) *)
  repeat rewrite length_app.
  simpl. reflexivity.
Qed.

Theorem step_preserves_length : 
  forall n l1 l2,
    step n l1 l2 -> length l1 = length l2.
Proof.
  intros n l1 l2 H.
  inversion H; subst.
  - (* Step_internal_case *)
    apply (step_internal_preserves_length n).
    assumption.
  - (* Step_final_case *)
    apply step_final_preserves_length.
    assumption.
Qed.

Inductive lex_lt : list nat -> list nat -> Prop :=
| lex_lt_nil : forall x xs, lex_lt [] (x :: xs)
| lex_lt_cons_lt : forall x y xs ys,
    x < y -> lex_lt (x :: xs) (y :: ys)
| lex_lt_cons_eq : forall x xs ys,
    lex_lt xs ys -> lex_lt (x :: xs) (x :: ys).

(* Lemma lex_lt_wf : well_founded lex_lt.
Proof.
Admitted. *)

Lemma step_internal_decreases_lex :
  forall n l1 l2,
    step_internal n l1 l2 ->
    lex_lt l2 l1.
Proof.
  intros n l1 l2 H.
  inversion H; subst; clear H.
  - (* StepInternalLong: prefix ++ x :: y :: suffix -> prefix ++ (x-1) :: (y+n) :: suffix *)
    induction prefix; simpl.
    + (* prefix = [] *)
      apply lex_lt_cons_lt.
      lia. (* x - 1 < x since x > 0 *)
    + (* prefix = a :: prefix' *)
      apply lex_lt_cons_eq.
      apply IHprefix.
  - (* StepInternalTwo: prefix ++ x :: [y] -> prefix ++ (x-1) :: [y] *)
    induction prefix; simpl.
    + (* prefix = [] *)
      apply lex_lt_cons_lt.
      lia. (* x - 1 < x since x > 0 *)
    + (* prefix = a :: prefix' *)
      apply lex_lt_cons_eq.
      apply IHprefix.
Qed.

Lemma step_final_decreases_lex :
  forall l1 l2,
    step_final l1 l2 ->
    lex_lt l2 l1.
Proof.
  intros l1 l2 H.
  inversion H; subst.
  (* l1 = prefix ++ [x], l2 = prefix ++ [x-1] *)
  clear H.
  induction prefix; simpl.
  - (* prefix = [] *)
    apply lex_lt_cons_lt.
    lia. (* x - 1 < x since x > 0 *)
  - (* prefix = a :: prefix' *)
    apply lex_lt_cons_eq.
    apply IHprefix.
Qed.

Theorem step_decreases_measure :
  forall n l1 l2,
    step n l1 l2 ->
    lex_lt l2 l1.
Proof.
  intros n l1 l2 H.
  inversion H; subst.
  - (* Step_internal_case *)
    apply (step_internal_decreases_lex n); assumption.
  - (* Step_final_case *)
    apply (step_final_decreases_lex); assumption.
Qed.

Definition binary_tree_depth2 : RoseTree :=
  Node 1 [
    Node 2 [ Node 4 []; Node 5 [] ];
    Node 3 [ Node 6 []; Node 7 [] ]
  ].

(* Evaluate the depth count for this tree *)
Eval compute in count_levels binary_tree_depth2.
Example step1 : step 2 [4; 2; 1] [3; 4; 1].
Proof.
  apply Step_internal_case.
  apply StepInternalLong with (prefix := []) (x := 4) (y := 2) (suffix := [1]).
  - lia. (* x > 0 *)
  - simpl. lia.
Qed.

Example step2 : step 2 [3; 4; 1] [2; 6; 1].
Proof.
  apply Step_internal_case.
  apply StepInternalLong with (prefix := []) (x := 3) (y := 4) (suffix := [1]).
  - lia. (* x > 0 *)
  - simpl. lia.
Qed.

Example step3 : step 2 [2; 6; 1] [1; 8; 1].
Proof.
  apply Step_internal_case.
  apply StepInternalLong with (prefix := []) (x := 2) (y := 6) (suffix := [1]).
  - lia. (* x > 0 *)
  - simpl. lia.
Qed.

Example step4 : step 2 [1; 8; 1] [0; 10; 1].
Proof.
  apply Step_internal_case.
  apply StepInternalLong with (prefix := []) (x := 1) (y := 8) (suffix := [1]).
  - lia. (* x > 0 *)
  - simpl. lia.
Qed.

Example step5 : step 2 [0; 10; 1] [0; 9; 1].
Proof.
  apply Step_internal_case.
  apply StepInternalTwo with (prefix := [0]) (x := 10) (y := 1).
  - lia. (* x > 0 *)
Qed.

Example step6 : step 2 [0; 9; 1] [0; 8; 1].
Proof.
  apply Step_internal_case.
  apply StepInternalTwo with (prefix := [0]) (x := 9) (y := 1).
  - lia. (* x > 0 *)
Qed.
