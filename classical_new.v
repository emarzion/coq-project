Set Implicit Arguments.

Require Import vecs_new.

(*Recovering classical first-order reasoning over finite domains*)
 
Definition decidable0(P : Prop) := P \/ ~ P.

Lemma or_dec0 : forall P Q : Prop, decidable0 P -> decidable0 Q -> decidable0 (P\/Q).
Proof.
  intros.
  destruct H.
  left; left; exact H.
  destruct H0.
  left; right; exact H0.
  right; intro.
  destruct H1; contradiction.
Qed.

Lemma impl_dec0 : forall P Q : Prop, decidable0 P -> decidable0 Q -> decidable0 (P -> Q).
Proof.
  intros.
  destruct H.
  destruct H0.
  left; intro; exact H0.
  right; intro.
  exact (H0 (H1 H)).
  left; intro; contradiction.
Qed.  

Definition decidable(X : Set)(P : X -> Prop) :=
  forall x : X, P x \/ ~ P x.

Definition decidable2(X : Set)(P : X -> X -> Prop) :=
  forall x y : X, P x y \/ ~ P x y.

Lemma or_dec1(X:Set)(P Q : X -> Prop) :
  decidable P -> decidable Q -> decidable (fun x => (P x \/ Q x)).
Proof.
  intros.
  intro x.
  destruct (H x).
  left; left; exact H1.
  destruct (H0 x).
  left; right; exact H2.
  right; intro.
  destruct H3; contradiction.
Qed.

Lemma impl_dec2(X : Set)(P Q : X -> X -> Prop) :
  decidable2 P -> decidable2 Q -> decidable2 (fun x y => ((P x y -> Q x y))).
Proof.
  intros H H0 x y.
  destruct (H x y).
  destruct (H0 x y).
  left; intro; exact H2.
  right; intro; absurd (Q x y).
  exact H2.
  apply H3; exact H1.
  left; intro; contradiction.
Qed.  

Lemma dec_neg : forall (X : Set)(P : X -> Prop),
  decidable P -> decidable (fun x => ~ P x).
Proof.
  intros.
  intro x.
  destruct (H x).
  right; intro.
  contradiction.
  left; exact H0.
Qed.

Definition hasExEM(X : Set) :=
  forall P : X -> Prop, decidable P -> 
   ((exists x:X, P x)\/~(exists x:X, P x)).

Definition hasQDP(X : Set) :=
  forall P : X -> Prop, decidable P -> 
  ((~forall x:X, P x) -> (exists x:X,~P x)).

Lemma ExEM_implies_QDP : forall X : Set,
  hasExEM X -> hasQDP X.
Proof.
  intros X H P HP H0.
  destruct (H (fun x => ~ P x)).
  exact (dec_neg HP).
  exact H1.
  elim H0.
  intro.
  destruct (HP x).
  exact H2.
  elim H1.
  exists x.
  exact H2.
Qed.

(*some stuff so that we can flip two universals in an row*)
Definition hasQDP2(X : Set) :=
  forall P : X -> X -> Prop, decidable2 P ->
  ((~forall x y:X, P x y) -> (exists x y:X, ~ P x y)).

Lemma ExEM_implies_QDP2 : forall X : Set,
  hasExEM X -> hasQDP2 X.
Proof.
  intros X H P HP H0.
  destruct (H (fun x => exists y, ~ P x y)).
  intro x.
  apply H.
  intro y.
  destruct (HP x y).
  right; intro; contradiction.
  left; exact H1.
  exact H1.
  elim H0.
  intros x y.
  destruct (HP x y).
  exact H2.
  elim H1.
  exists x,y.
  exact H2.
Qed.

Lemma empty_hasExEM : hasExEM empty.
Proof.
  intros P HP.
  right; intro.
  destruct H.
  destruct x.
Qed.

Lemma unit_hasExEM : hasExEM unit.
Proof.
  intros P HP.
  destruct (HP tt).
  left; exists tt; exact H.
  right; intro.
  destruct H0.
  destruct x.
  contradiction.
Qed.

Lemma bool_hasExEM : hasExEM bool.
Proof.
  intros P HP.
  destruct (HP false).
  left; exists false; exact H.
  destruct (HP true).
  left; exists true; exact H0.
  right; intro.
  destruct H1.
  destruct x; contradiction.
Qed.

Lemma dec_l : forall (A B : Set)(P : A + B -> Prop),
  decidable P -> decidable (fun x => P (inl x)).
Proof.
  intros.
  intro x.
  apply H.
Qed.

Lemma dec_r : forall (A B : Set)(P : A + B -> Prop),
  decidable P -> decidable (fun x => P (inr x)).
Proof.
  intros.
  intro x.
  apply H.
Qed.

Lemma sum_ExEM : forall A B : Set, hasExEM A -> hasExEM B -> hasExEM (A+B).
Proof.
  intros.
  intros P H1.
  destruct (H (fun x => P (inl x))).
  exact (dec_l H1).
  destruct H2.
  left; exists (inl x); exact H2.
  destruct (H0 (fun y => P (inr y))).
  exact (dec_r H1).
  destruct H3.
  left; exists (inr x); exact H3.
  right; intro.
  destruct H4.
  destruct x.
  apply H2.
  exists a; exact H4.
  apply H3.
  exists b; exact H4.
Qed.

Lemma finExEM : forall n:nat, hasExEM(fin n).
Proof.
  induction n.
  apply empty_hasExEM.
  simpl.
  apply sum_ExEM.
  apply unit_hasExEM.
  exact IHn.
Qed.

Lemma finQDP : forall n:nat, hasQDP(fin n).
Proof.
  intro n.
  apply ExEM_implies_QDP.
  apply finExEM.
Qed.

Lemma prod_ExEM : forall A B : Set, hasExEM A -> hasExEM B -> hasExEM (A*B).
Proof.
  intros A B HA HB P HP.
  destruct (HA (fun a => exists b, P (a,b))).
  intro a.
  apply HB.
  intro b.
  apply HP.
  left.
  destruct H as [a [b H0]].
  exists (a,b); exact H0.
  right; intro.
  apply H.
  destruct H0 as [[a b] H0].
  exists a,b; exact H0.
Qed.

Lemma vec_bool_ExEM : forall n:nat, hasExEM (vec bool n).
Proof.
  induction n.
  apply unit_hasExEM.
  simpl.
  apply prod_ExEM.
  apply bool_hasExEM.
  exact IHn.
Qed.

Lemma vec_bool_QDP : forall n:nat, hasQDP (vec bool n).
Proof.
  intro; apply ExEM_implies_QDP; apply vec_bool_ExEM.
Qed.

Lemma vec_bool_QDP2 : forall n:nat, hasQDP2 (vec bool n).
Proof.
  intro; apply ExEM_implies_QDP2; apply vec_bool_ExEM.
Qed.