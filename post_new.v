Set Implicit Arguments.

Require Import Coq.Bool.Bool.
Require Import vecs_new.
Require Import andnot_new.
Require Import classical_new.

Lemma bool_destr : forall b, b = false \/ b = true.
Proof.
  destruct b.
  right; reflexivity.
  left; reflexivity.
Qed.

Definition f_vec (n : nat) : vec bool n :=
  const_vec n false.

Definition t_vec (n : nat) : vec bool n :=
  const_vec n true.

Definition f_preserving (n : nat) (g : conn n) :=
  g (f_vec n) = false.

Definition t_preserving (n : nat) (g : conn n) :=
  g (t_vec n) = true.

(* takes [x1,...xk] => [negb x1,..., negb xk] *)
Fixpoint negated (k : nat) : vec bool k -> vec bool k := 
  match k as k return vec bool k -> vec bool k with
    0   => fun _ => (tt : vec bool 0)
  | S l => fun v => (negb (vhead v) , negated l (vtail v) )
  end.

Lemma negated_invol : forall (n : nat)(v : vec bool n),
  negated n (negated n v) = v.
Proof.
  intros.
  induction n.
  destruct v; simpl.
  reflexivity.
  destruct v.
  simpl.
  rewrite negb_involutive.
  rewrite IHn.
  reflexivity.
Qed.

Lemma negated_correct : forall (n : nat)(v : vec bool n)(i : fin n),
  item_at bool n i (negated n v) = negb (item_at bool n i v).
Proof.
  intros.
  induction n.
  destruct i.
  destruct v.
  destruct i.
  destruct u.
  simpl.
  reflexivity.
  simpl.
  apply IHn.
Qed.

Definition dual (n : nat) (g : conn n) :=
  fun v : vec bool n => negb (g (negated n v)).

Definition self_dual (n : nat)(g : conn n) : Prop :=
  g [=] dual g.

Definition monotone (n : nat) (g : conn n) :=
  forall x y : vec bool n, 
  vec_le n x y -> 
  bool_le (g x) (g y).

Lemma bool_le_dec : decidable2 bool_le.
Proof.
  intro b.
  destruct b.
  intro c.
  destruct c.
  left; simpl; reflexivity.
  right; simpl; intro; exact H.
  simpl.
  intro; left; reflexivity.
Qed.

Lemma le_dec : forall n : nat, decidable2 (vec_le n).
Proof.
  induction n.
  intros v w.
  simpl; left; reflexivity.
  intros v w.
  destruct v as [b v'], w as [c w'].
  destruct b.
  destruct c.
  destruct (IHn v' w').
  left; simpl.
  split.
  reflexivity.
  exact H.
  right; simpl.
  intro.
  apply H.
  apply H0.
  right; simpl.
  intro.
  apply H.
  destruct (IHn v' w').
  left.
  simpl.
  split.
  reflexivity.
  exact H.
  right.
  simpl.
  intro.
  apply H.
  apply H0.
Qed.

Fixpoint neg_at (n : nat) : vec bool n -> fin n -> vec bool n :=
  match n as n return vec bool n -> fin n -> vec bool n with
   0     => fun v i => (emptyf (vec bool 0) i)
  |(S m) => fun v i => match i with
                          inl tt => (negb (vhead v), (vtail v))
                         |inr j  => (vhead v , neg_at m (vtail v) j)
                       end
  end.

Lemma neg_at_correct : forall (n : nat)(v : vec bool n)(i : fin n),
  (item_at bool n i (neg_at n v i)) = negb (item_at bool n i v).
Proof.
  intros.
  induction n.
  destruct i.
  destruct v as [b w].
  destruct i.
  destruct u.
  simpl; reflexivity.
  simpl.
  apply IHn.
Qed.

Lemma neg_at_invol : forall (n : nat)(v : vec bool n)(i : fin n),
  v = neg_at n (neg_at n v i) i.
Proof.
  intros.
  induction n.
  destruct i.
  destruct v as [b w].
  destruct i.
  destruct u.
  simpl.
  rewrite negb_involutive; reflexivity.
  simpl.
  rewrite <- IHn.
  reflexivity.
Qed.

Definition is_dummy (n :nat) (g : conn n) (i : fin n) : Prop :=
  forall v : vec bool n, 
  g v = g (neg_at n v i).

Definition is_counted (n :nat) (g : conn n) (i : fin n) : Prop :=
  forall v : vec bool n, 
  g v = negb (g (neg_at n v i)).

Definition counting (n : nat) (g : conn n) :=
  forall i : fin n, 
  (is_dummy g i) \/ (is_counted g i).

Definition non_fp_def(X : forall n:nat, conn n -> Prop) := 
  exists (n:nat)(f:conn n), ~f_preserving f /\ Definable X f.
Definition non_tp_def(X : forall n:nat, conn n -> Prop) := 
  exists (n:nat)(f:conn n), ~t_preserving f /\ Definable X f.
Definition non_monotone_def(X : forall n:nat, conn n -> Prop) :=
  exists (n:nat)(f:conn n), ~monotone f /\ Definable X f.
Definition non_selfdual_def(X : forall n:nat, conn n -> Prop) :=
  exists (n:nat)(f:conn n), ~self_dual f /\ Definable X f.
Definition non_counting_def(X : forall n:nat, conn n -> Prop) :=
  exists (n:nat)(f:conn n), ~counting f /\ Definable X f.

(* idea: fun x => f(x,....x) *)
Definition diag(n : nat) : conn n -> conn 1 :=
  fun f => comp 1 f (const_vec n ID).

Lemma diag_def(X : forall n:nat, conn n -> Prop) : forall (n : nat)(f : conn n), Definable X f -> Definable X (diag f).
Proof.
  intros.
  apply compose.
  exact H.
  intros.
  rewrite const_vec_constant.
  apply id_def.
Qed.

Lemma ID_cons_vec(n : nat)(x : bool) : vec_ap bool n (const_vec n ID) (x,tt) = const_vec n x.
Proof.
  apply vec_ext.
  intro i.
  rewrite vec_ap_lemma.
  rewrite const_vec_constant.
  rewrite const_vec_constant.
  simpl.
  reflexivity.
Qed.

(* first part of Lemma 1 from the paper *)
Lemma non_fp_non_tp_TF_or_NOT(X : forall n:nat, conn n -> Prop) : non_fp_def X -> non_tp_def X -> 
  (Definable X NOT) \/ (Definable X (const 1 true) /\ Definable X (const 1 false)).
Proof.
  intros.
  destruct H as [m [f [H_f D_f]]].
  destruct H0 as [n [g [H_g D_g]]].
  assert (Definable X (diag f)).
  apply diag_def; exact D_f.
  assert (Definable X (diag g)).
  apply diag_def; exact D_g.
  assert (diag f [false] = negb false).
  unfold diag.
  unfold comp.
  rewrite ID_cons_vec.
  unfold f_preserving, f_vec in H_f.
  destruct (f (const_vec m false)).
  reflexivity.
  elim H_f; reflexivity.
  simpl in H1.
  destruct (bool_destr (diag f [true])).
  left.
  apply (def_ext H).
  intro x.
  destruct x.
  destruct b,v.
  exact H2.
  exact H1.
  assert (diag g [true] = negb true).
  unfold diag.
  unfold comp.
  rewrite ID_cons_vec.
  unfold t_preserving, t_vec in H_g.
  destruct (g (const_vec n true)).
  elim H_g; reflexivity.
  reflexivity.
  simpl in H3.
  destruct (bool_destr (diag g [false])).
  right.
  split.
  apply (def_ext H).
  destruct v.
  destruct b,v.
  exact H2.
  exact H1.
  apply (def_ext H0).
  destruct v.
  destruct b,v.
  exact H3.
  exact H4.
  left.
  apply (def_ext H0).
  destruct v.
  destruct b,v.
  exact H3.
  exact H4.
Qed.

(* Given two booleans, outputs the unary connective with that truth table*)
Fixpoint ttable_func(x : bool * bool) : conn 1 :=
  match x with
  |(false , false) => (const 1 false)
  |(false , true ) => ID
  |(true , false ) => NOT
  |(true , true  ) => (const 1 true)
  end.

Fixpoint vec_prod(n : nat) : vec bool n -> vec bool n -> vec (bool * bool) n :=
  match n as n return vec bool n -> vec bool n -> vec (bool * bool) n with
   0     => fun _ _ => (tt : vec (bool * bool) 0)
  |(S m) => fun v w => ( ((vhead v),(vhead w)) , vec_prod m (vtail v) (vtail w))
  end.

Fixpoint star(n : nat) : vec bool n -> vec bool n -> vec (conn 1) n :=
  match n as n return vec bool n -> vec bool n -> vec (conn 1) n with
    0     => fun _ _ => (tt : vec (conn 1) 0)
   |(S m) => fun v w => (ttable_func (vhead v, vhead w) , star m (vtail v) (vtail w))
  end.

Lemma star_vec_app1 : forall (n : nat)(v w : vec bool n),
  vec_ap bool n (star n v w) [false] = v.
Proof.
  induction n.
  intros.
  simpl.
  destruct v; reflexivity.
  intros.
  destruct v as [b v'].
  destruct w as [c w'].
  simpl.
  rewrite IHn.
  destruct b,c; reflexivity.
Qed.

Lemma star_vec_app2 : forall (n : nat)(v w : vec bool n),
  vec_ap bool n (star n v w) [true] = w.
Proof.
  induction n.
  intros.
  simpl.
  destruct w; reflexivity.
  intros.
  destruct v as [b v'].
  destruct w as [c w'].
  simpl.
  rewrite IHn.
  destruct b,c; reflexivity.
Qed.

Lemma non_mon_witnesses : forall (n : nat)(f : conn n), ~monotone f -> exists v w : vec bool n,
  vec_le n v w /\ f v = true /\ f w = false.
Proof.
  intros.
  assert (exists v w, ~(vec_le n v w -> bool_le (f v) (f w))).
  apply vec_bool_QDP2.
  apply impl_dec2.
  apply le_dec.
  intros x y.
  apply bool_le_dec.
  exact H.
  destruct H0 as [v [w H1]].
  exists v,w.
  split.
  destruct (le_dec n v w).
  exact H0.
  elim H1.
  intro; contradiction.
  split.
  destruct (f v).
  reflexivity.
  elim H1.
  intros; simpl; reflexivity.
  destruct (f w).
  elim H1.
  intros.
  destruct (f v); reflexivity.
  reflexivity.  
Qed.

Lemma star_cases_le : forall (n : nat)(v w : vec bool n)(i : fin n),  vec_le n v w ->
   ((const 1 false) = item_at (conn 1) n i (star n v w)) \/ 
   (             ID = item_at (conn 1) n i (star n v w)) \/
   ( (const 1 true) = item_at (conn 1) n i (star n v w)).
Proof.
  intros.
  induction n.
  destruct i.
  destruct v as [b v'], w as [c w'].
  destruct i.
  destruct b,c,u; simpl.
  right; right; reflexivity.
  simpl in H.
  destruct H; contradiction.
  right; left; reflexivity.
  left; reflexivity.
  simpl.
  apply IHn.
  apply H.  
Qed.  

Lemma NOT_defined(X : forall n:nat, conn n -> Prop) : non_fp_def X -> non_tp_def X -> non_monotone_def X -> Definable X NOT.
Proof.
  intros.
  destruct (non_fp_non_tp_TF_or_NOT H H0).
  exact H2.
  destruct H2.
  destruct H1 as [n [f [f_not f_def]]].
  destruct (non_mon_witnesses f_not) as [v [w [v_le_w [v_val w_val]]]].
  assert (Definable X (comp 1 f (star n v w))).
  apply compose.
  exact f_def.
  intro.
  destruct (star_cases_le n v w i v_le_w).
  rewrite <- H1; exact H3.
  destruct H1.
  rewrite <- H1; apply id_def.
  rewrite <- H1; exact H2.
  apply (def_ext H1).
  intro x.
  destruct x.
  destruct v0.
  destruct b.
  unfold comp; rewrite star_vec_app2.
  rewrite w_val; reflexivity.
  unfold comp; rewrite star_vec_app1.
  rewrite v_val; reflexivity.
Qed.

Lemma non_dual_witness : forall (n : nat)(f : conn n),~self_dual f -> exists v : vec bool n,
  f v = f (negated n v).
Proof.
  intros.
  cut (exists v : vec bool n, ~~f v = f (negated n v)).
  intro.
  destruct H0.
  exists x.
  destruct (bool_dec (f x) (f (negated n x))).
  exact e.
  contradiction.
  apply vec_bool_QDP.
  intro.
  destruct (bool_dec (f x) (f (negated n x))).
  right; intro; contradiction.
  left; exact n0.
  intro.
  absurd ((forall v : vec bool n, f v = negb (f (negated n v)))).
  exact H.
  intro.
  destruct (bool_dec (f v) (f (negated n v))).
  elim (H0 v).
  exact e.
  destruct (f v) , (f (negated n v)).
  elim n0; reflexivity.
  reflexivity.
  reflexivity.
  elim  n0; reflexivity.
Qed.

Lemma star_cases_negated : forall (n : nat)(v : vec bool n)(i : fin n),
   (ID  = item_at (conn 1) n i (star n v (negated n v))) \/
   (NOT = item_at (conn 1) n i (star n v (negated n v))).
Proof.
  intros.
  induction n.
  destruct i.
  destruct v as [b w].
  destruct i.
  destruct b,u.
  simpl.
  right; reflexivity.
  simpl.
  left; reflexivity.
  simpl.
  apply IHn.
Qed.

Lemma F_defined(X : forall n:nat, conn n -> Prop) : non_fp_def X -> non_tp_def X -> non_monotone_def X -> non_selfdual_def X
  -> Definable X (const 1 false).
Proof.
  intros.
  pose (NOT_defined H H0 H1) as not_def.
  destruct H2 as [n [f [f_not f_def]]].
  assert (exists v : vec bool n,  f v = f (negated n v)).
  apply non_dual_witness.
  exact f_not.
  destruct H2 as [v f_eq].
  assert (Definable X (comp 1 f (star n v (negated n v)))).
  apply compose.
  exact f_def.
  intro i.
  destruct (star_cases_negated n v i).
  rewrite <- H2; apply id_def.
  rewrite <- H2; exact not_def.
  destruct (bool_destr (f v)).
  apply (def_ext H2).
  intro x.
  unfold comp.
  destruct x.
  destruct b,v0.  
  rewrite star_vec_app2.
  rewrite <- f_eq; rewrite H3; reflexivity.
  rewrite star_vec_app1.
  rewrite H3; reflexivity.
  assert (Definable X (comp 1 NOT [comp 1 f (star n v (negated n v)) ] )).
  apply unit_comp_def.
  exact not_def.
  apply compose.
  exact f_def.
  intro i.
  destruct (star_cases_negated n v i).
  rewrite <- H4; apply id_def.
  rewrite <- H4; exact not_def.
  apply (def_ext H4).
  intro x.
  unfold comp.
  destruct x.
  destruct b,v0.
  simpl.
  rewrite star_vec_app2.
  rewrite <- f_eq; rewrite H3; reflexivity.
  simpl.
  rewrite star_vec_app1.
  rewrite H3; reflexivity.
Qed.

Lemma T_defined(X : forall n:nat, conn n -> Prop) : non_fp_def X -> non_tp_def X -> non_monotone_def X -> non_selfdual_def X
  -> Definable X (const 1 true).
Proof.
  intros.
  pose (NOT_defined H H0 H1) as not_def.
  pose (F_defined H H0 H1 H2) as f_def.
  assert (Definable X (comp 1 NOT [const 1 false])).
  apply unit_comp_def.
  exact not_def.
  exact f_def.
  apply (def_ext H3).
  intro x.
  unfold comp.
  reflexivity.
Qed.

Fixpoint neg_vec (n : nat) : fin n -> vec (conn 1) (S n) :=
  match n as n return fin n -> vec (conn 1) (S n) with
  |0     => fun i => emptyf (vec (conn 1) 1) i
  |(S m) => fun i => match i with
                     |inl u => (NOT , const_vec (S m) ID )
                     |inr j => (ID  , (neg_vec m j)      )
                     end
  end.

Lemma dummy_dec : forall (n:nat)(f : conn n)(i : fin n),
  is_dummy f i \/ ~is_dummy f i.
Proof.
  intros.
  unfold is_dummy.
  assert ((exists v, f v <> f (neg_at n v i))\/(~exists v, f v <> f (neg_at n v i))).
  apply vec_bool_ExEM.
  intro.
  destruct (bool_dec (f x) (f (neg_at n x i))).
  right; intro; contradiction.
  left; exact n0.
  destruct H.
  right.
  intro.
  destruct H as [v Hv].
  apply Hv.
  apply H0.
  left.
  intro.
  destruct (bool_dec (f v) (f (neg_at n v i))).
  exact e.
  elim H.
  exists v; exact n0.
Qed.

Lemma count_dec : forall (n:nat)(f : conn n)(i : fin n),
  is_counted f i \/ ~is_counted f i.
Proof.
  intros.
  unfold is_counted.
  assert ((exists v, f v <> negb (f (neg_at n v i)))\/(~exists v, f v <> negb (f (neg_at n v i)))).
  apply vec_bool_ExEM.
  intro.
  destruct (bool_dec (f x) (negb (f (neg_at n x i)))).
  right; intro; contradiction.
  left; exact n0.
  destruct H.
  right; intro.
  destruct H as [v Hv].
  apply Hv.
  apply H0.
  left.
  intro.
  destruct (bool_dec (f v) (f (neg_at n v i))).
  elim H.
  exists v.
  intro.
  rewrite <- e in H0.
  symmetry in H0.
  exact (no_fixpoint_negb (f v) H0).
  destruct (f v) , (f  (neg_at n v i)).
  elim n0; reflexivity.
  reflexivity.
  reflexivity.
  elim n0; reflexivity.
Qed.

Lemma non_counting_index : forall (n : nat)(f : conn n), ~counting f ->
  exists i, (~is_dummy f i)/\(~is_counted f i).
Proof.
  intros.
  assert (exists i, ~(is_dummy f i \/ is_counted f i)).
  apply finQDP.
  intro.
  apply or_dec0.
  apply dummy_dec.
  apply count_dec.
  exact H.
  destruct H0 as [i H0].
  exists i.
  tauto.
Qed.

Lemma dummy_vec_witness : forall (n : nat)(f : conn n)(i : fin n),
   ~is_dummy f i -> exists v, f v <> f (neg_at n v i).
Proof.
  intros.
  apply vec_bool_QDP.
  intro.
  destruct (bool_dec (f x)  (f (neg_at n x i))).
  left; exact e.
  right; exact n0.
  exact H.
Qed.

Lemma count_vec_witness : forall (n : nat)(f : conn n)(i : fin n),
  ~is_counted f i -> exists v, f v = f (neg_at n v i).
Proof.
  intros.
  assert (exists v, ~f v = negb ( f (neg_at n v i))).
  apply vec_bool_QDP.
  intro.
  destruct (bool_dec (f x) (f (neg_at n x i))).
  right; rewrite e.
  intro; symmetry in H0.
  apply (no_fixpoint_negb (f (neg_at n x i)) H0).
  left; destruct (f x) , (f (neg_at n x i)).
  elim n0; reflexivity.
  reflexivity.
  reflexivity.
  elim n0; reflexivity.
  exact H.
  destruct H0 as [v Hv].
  exists v.
  destruct (f v),(f (neg_at n v i)).
  reflexivity.
  elim Hv; reflexivity.
  elim Hv; reflexivity.
  reflexivity.
Qed.

Lemma non_counting_witnesses : forall (n : nat)(f : conn n),
  ~counting f -> exists (i : fin n)(v w : vec bool n),
   f v <> f (neg_at n v i) /\ (f w = f (neg_at n w i)).
Proof.
  intros.
  destruct (non_counting_index H) as [i [Hd Hc]].
  destruct (dummy_vec_witness Hd) as [v Hv].
  destruct (count_vec_witness Hc) as [w Hw].
  exists i,v,w.
  split.
  exact Hv.
  exact Hw.
Qed.

(*WLOG we want the the component at index i to be F to simplify matters. *)
Lemma non_counting_witnesses_F : forall (n : nat)(f : conn n),
  ~counting f -> exists (i : fin n)(v w : vec bool n),
   item_at bool n i v = false /\ item_at bool n i w = false /\
   f v <> f (neg_at n v i) /\ (f w = f (neg_at n w i)).
Proof.
  intros.
  destruct (non_counting_witnesses H) as [i [v [w [Hv Hw]]]].
  destruct (bool_destr (item_at bool n i v)).
  destruct (bool_destr (item_at bool n i w)).
  exists i,v,w.
  tauto.
  exists i,v,(neg_at n w i).
  split.
  exact H0.
  split.
  rewrite neg_at_correct.
  rewrite H1; reflexivity.
  split.
  exact Hv.
  rewrite <-neg_at_invol.
  symmetry; exact Hw.
  destruct (bool_destr (item_at bool n i w)).
  exists i,(neg_at n v i),w.
  split.
  rewrite neg_at_correct.
  rewrite H0; reflexivity.
  split.
  exact H1.
  split.
  rewrite <-neg_at_invol.
  intro.
  apply Hv.
  symmetry; exact H2.
  exact Hw.
  exists i,(neg_at n v i),(neg_at n w i).
  split.
  rewrite neg_at_correct.
  rewrite H0; reflexivity.
  split.
  rewrite neg_at_correct.
  rewrite H1; reflexivity.
  split.
  rewrite <-neg_at_invol.
  intro.
  apply Hv.
  symmetry; exact H2.
  rewrite <- neg_at_invol.
  symmetry; exact Hw.
Qed.

Fixpoint star2(n : nat) : vec bool n -> vec bool n -> vec (conn 2) n :=
  match n as n return vec bool n -> vec bool n -> vec (conn 2) n with
    0     => fun _ _ => (tt : vec (conn 2) 0)
   |(S m) => fun v w => (comp 2 (ttable_func (fst v,fst w)) [p1] , star2 m (snd v) (snd w))
  end.

Lemma star2_def(X : forall n:nat, conn n -> Prop)(n : nat)(v w : vec bool n) : 
  Definable X NOT -> Definable X (fun x:(vec bool 1) => false) -> Definable X (fun x:(vec bool 1) => true) ->
  forall i : fin n, Definable X (item_at (conn 2) n i (star2 n v w)).
Proof.
  intros.
  induction n.
  destruct i.
  destruct i.
  destruct v,w.
  destruct b,b0,u; simpl.
  apply unit_comp_def.
  exact H1.
  apply project.
  apply unit_comp_def.
  exact H.
  apply project.
  apply unit_comp_def.
  apply id_def.
  apply project.
  apply unit_comp_def.
  apply H0.
  apply project.
  simpl.
  apply IHn.
Qed.

Lemma star2_F : forall (n : nat)(v w : vec bool n)(b : bool), 
  vec_ap bool n (star2 n v w) [false , b] = v.
Proof.
  intros.
  induction n.
  simpl.
  destruct v; reflexivity.
  destruct v,w.
  destruct b0,b1; simpl; unfold comp; simpl; rewrite IHn; reflexivity.
Qed.

Lemma star2_T : forall (n : nat)(v w : vec bool n)(b : bool), 
  vec_ap bool n (star2 n v w) [true , b] = w.
Proof.
  intros.
  induction n.
  simpl.
  destruct w; reflexivity.
  destruct v,w.
  destruct b0,b1; simpl; unfold comp; simpl; rewrite IHn; reflexivity.
Qed.

Fixpoint star_mod(n : nat) : vec bool n -> vec bool n -> fin n -> vec (conn 2) n :=
  match n as n return vec bool n -> vec bool n -> fin n -> vec (conn 2) n with
    0     => fun v w i => emptyf (vec (conn 2) 0) i
   |(S m) => fun v w i => match i with
                             inl u => (p2,star2 m (vtail v) (vtail w))
                            |inr j => ((comp 2 (ttable_func (fst v,fst w)) [ p1 ]), star_mod m (snd v)(snd w) j)
                          end
  end.

Lemma star_mod_def(X : forall n:nat, conn n -> Prop)(n : nat)(v w : vec bool n) : 
  Definable X NOT -> Definable X (fun x:(vec bool 1) => false) -> Definable X (fun x:(vec bool 1) => true) ->
  forall i j: fin n, Definable X (item_at (conn 2) n j (star_mod n v w i)).
Proof.
  intros.
  induction n.
  destruct i.
  destruct v,w.
  destruct i,j.
  destruct u,u0; simpl.
  apply project.
  simpl.
  apply star2_def.
  exact H.
  exact H0.
  exact H1.
  destruct u.
  destruct b,b0.
  simpl.
  apply unit_comp_def.
  exact H1.
  apply project.
  simpl.
  apply unit_comp_def.
  exact H.
  apply project.
  simpl.
  apply unit_comp_def.
  apply id_def.
  apply project.
  simpl.
  apply unit_comp_def.
  exact H0.
  apply project.
  simpl.
  apply IHn.
Qed.  

Lemma star_mod_FF(n : nat)(v w : vec bool n)(i : fin n) :
  item_at bool n i v = false -> item_at bool n i w = false ->
  vec_ap bool n (star_mod n v w i) [false , false] = v.
Proof.
  intros.
  induction n.
  destruct i.
  destruct i,v,w.
  destruct b,u; simpl.
  discriminate H.
  destruct b0; simpl.
  discriminate H0.
  unfold p2, proj.
  simpl.
  rewrite star2_F; reflexivity.
  destruct b,b0.
  simpl.
  unfold comp, const; rewrite IHn.
  reflexivity.
  exact H.
  exact H0.
  simpl.
  unfold comp, const; rewrite IHn.
  simpl; reflexivity.
  exact H.
  exact H0.
  simpl.
  unfold comp; rewrite IHn.
  simpl; reflexivity.
  exact H.
  exact H0.
  simpl.
  unfold comp, const; rewrite IHn.
  reflexivity.
  exact H.
  exact H0.
Qed.

Lemma star_mod_TF(n : nat)(v w : vec bool n)(i : fin n) :
  item_at bool n i v = false -> item_at bool n i w = false ->
  vec_ap bool n (star_mod n v w i) [true , false] = w.
Proof.
  intros.
  induction n.
  destruct i.
  destruct i,v,w.
  destruct b,u; simpl.
  discriminate H.
  destruct b0; simpl.
  discriminate H0.
  unfold p2, proj.
  simpl.
  rewrite star2_T; reflexivity.
  destruct b,b0.
  simpl.
  unfold comp, const; rewrite IHn.
  reflexivity.
  exact H.
  exact H0.
  simpl.
  unfold comp, const; rewrite IHn.
  simpl; reflexivity.
  exact H.
  exact H0.
  simpl.
  unfold comp; rewrite IHn.
  simpl; reflexivity.
  exact H.
  exact H0.
  simpl.
  unfold comp, const; rewrite IHn.
  reflexivity.
  exact H.
  exact H0.
Qed.

Lemma star_mod_bT(n : nat)(v w : vec bool n)(i : fin n)(b : bool) :
  neg_at n (vec_ap bool n (star_mod n v w i) [ b , true]) i = 
  (vec_ap bool n (star_mod n v w i) [ b , false]).
Proof.
  induction n.
  destruct i.
  destruct v,w,i.
  destruct u,b0,b1.
  simpl.
  unfold p2,proj.
  simpl.
  destruct b.
  rewrite star2_T.
  rewrite star2_T.
  reflexivity.
  rewrite star2_F.
  rewrite star2_F.
  reflexivity.
  simpl.
  unfold p2,proj.
  simpl.
  destruct b.
  rewrite star2_T.
  rewrite star2_T.
  reflexivity.
  rewrite star2_F.
  rewrite star2_F.
  reflexivity.
  simpl.
  unfold p2,proj.
  simpl.
  destruct b.
  rewrite star2_T.
  rewrite star2_T.
  reflexivity.
  rewrite star2_F.
  rewrite star2_F.
  reflexivity.
  simpl.
  unfold p2,proj.
  simpl.
  destruct b.
  rewrite star2_T.
  rewrite star2_T.
  reflexivity.
  rewrite star2_F.
  rewrite star2_F.
  reflexivity.
  simpl.
  unfold comp.
  unfold p1,proj.
  simpl.
  destruct b0; destruct b1; rewrite IHn; reflexivity.
Qed.

Lemma star_mod_bT2(n : nat)(v w : vec bool n)(i : fin n)(b : bool) :
  (vec_ap bool n (star_mod n v w i) [b , true]) = 
   neg_at n (vec_ap bool n (star_mod n v w i) [b , false]) i.
Proof.
  rewrite (neg_at_invol n (vec_ap bool n (star_mod n v w i) [b , true]) i).
  f_equal.
  apply star_mod_bT.
Qed.

Definition one_F(f : conn 2) := exists v,
  (f v = false /\ forall w, w<>v -> f w = true).

Definition one_T(f : conn 2) := exists v,
  (f v = true /\ forall w, w<>v -> f w = false).

Lemma odd_from_not_counting(X : forall n:nat, conn n -> Prop) : 
  Definable X NOT -> Definable X (fun x:(vec bool 1) => false) -> Definable X (fun x:(vec bool 1) => true) ->
  non_counting_def X ->
  exists g : conn 2, Definable X g /\ (one_F g \/ one_T g).
Proof.
  intros.
  destruct H2 as [n [f [f_nc f_def]]].
  destruct (non_counting_witnesses_F f_nc) as [i [v [w [v_i [w_i [Hnd Hnc]]]]]].
  exists (comp 2 f (star_mod n v w i)).
  split.
  apply compose.
  exact f_def.
  apply star_mod_def.
  exact H.
  exact H0.
  exact H1.
  destruct  (bool_destr (f w)).
  destruct (bool_destr (f v)).
  right.
  exists [false , true].
  split.
  unfold comp.
  rewrite star_mod_bT2.
  rewrite (star_mod_FF n v w i v_i w_i).
  apply not_false_is_true.
  intro; apply Hnd.
  rewrite H3; symmetry; exact H4.
  intro x.
  destruct x as (b,(b0,v0)).
  destruct b,b0,v0.
  intro.
  unfold comp.
  rewrite star_mod_bT2.
  rewrite (star_mod_TF n v w i v_i w_i).
  rewrite <- Hnc; exact H2.
  intro.
  unfold comp.
  rewrite star_mod_TF.
  exact H2.
  exact v_i.
  exact w_i.
  intro.
  elim H4; reflexivity.
  intro.
  unfold comp.
  rewrite star_mod_FF.
  exact H3.
  exact v_i.
  exact w_i.
  right.
  exists [false , false].
  split.
  unfold comp.
  rewrite (star_mod_FF n v w i v_i w_i).
  exact H3.
  intro x; destruct x as (b,(b0,v0)).
  destruct b,b0,v0.
  intro.
  unfold comp.
  rewrite star_mod_bT2.
  rewrite (star_mod_TF n v w i v_i w_i).
  rewrite <- Hnc; exact H2.
  intro.
  unfold comp.
  rewrite star_mod_TF.
  exact H2.
  exact v_i.
  exact w_i.
  intro.
  unfold comp.
  rewrite star_mod_bT2.
  rewrite (star_mod_FF n v w i v_i w_i).
  apply not_true_is_false.
  intro.
  apply Hnd.
  rewrite H5; exact H3.
  intro.
  elim H4.
  reflexivity.
  destruct (bool_destr (f v)).
  left.
  exists [false, false].
  split.
  unfold comp.
  rewrite (star_mod_FF n v w i v_i w_i).
  exact H3.
  intro x; destruct x as (b,(b0,v0)).
  destruct b,b0,v0.
  intro.
  unfold comp.
  rewrite star_mod_bT2.
  rewrite (star_mod_TF n v w i v_i w_i).
  rewrite <- Hnc; exact H2.
  intro.
  unfold comp.
  rewrite star_mod_TF.
  exact H2.
  exact v_i.
  exact w_i.
  intro.
  unfold comp.
  rewrite star_mod_bT2.
  rewrite (star_mod_FF n v w i v_i w_i).
  apply not_false_is_true.
  intro.
  apply Hnd.
  rewrite H5; exact H3.
  intro.
  elim H4; reflexivity.
  left.
  exists [false , true].
  split.
  unfold comp.
  rewrite star_mod_bT2.
  rewrite (star_mod_FF n v w i v_i w_i).
  apply not_true_is_false.
  intro.
  apply Hnd.
  rewrite H4; exact H3.
  intro x; destruct x as (b,(b0,v0)).
  destruct b,b0,v0.
  intro.
  unfold comp.
  rewrite star_mod_bT2.
  rewrite (star_mod_TF n v w i v_i w_i).
  rewrite <- Hnc; exact H2.
  intro.
  unfold comp.
  rewrite star_mod_TF.
  exact H2.
  exact v_i.
  exact w_i.
  intro.
  elim H4; reflexivity.
  intro.
  unfold comp.
  rewrite star_mod_FF.
  exact H3.
  exact v_i.
  exact w_i.
Qed.

Lemma neg_one_F_one_T : forall f, one_F f -> one_T (comp 2 NOT [ f ]).
Proof.
  intros.
  destruct H as [v [Hv Hw]].
  exists v.
  split.
  unfold comp.
  simpl.
  rewrite Hv; reflexivity.
  intros.
  unfold comp.
  simpl.
  rewrite (Hw w H).
  reflexivity.
Qed.

Lemma one_FT_to_one_T(X : forall n:nat, conn n -> Prop) : 
  Definable X NOT -> (exists f, Definable  X f /\ (one_F f \/ one_T f)) -> (exists f, Definable X f /\ one_T f).
Proof.
  intros.
  destruct H0 as [f H0].
  destruct H0.
  destruct H1.
  exists (comp 2 NOT [f] ).
  split.
  apply unit_comp_def.
  exact H.
  exact H0.
  apply (neg_one_F_one_T H1).
  exists f.
  split.
  exact H0.
  exact H1.
Qed.

Lemma odd_and_def(X : forall n:nat, conn n -> Prop) : Definable X NOT -> (exists f, Definable  X f /\ (one_F f \/ one_T f))
  -> Definable X AND.
Proof.
  intros.
  destruct (one_FT_to_one_T H H0) as [f [Hdef [v [Hv Hw]]]].
  destruct v as (b,(b0,v0)).
  destruct b,b0,v0.
  apply (def_ext Hdef).
  intro v.
  destruct v as (c,(c0,w0)).
  destruct c,c0,w0.
  rewrite Hv; reflexivity.
  rewrite Hw.
  reflexivity.
  discriminate.
  rewrite Hw.
  reflexivity.
  discriminate.
  rewrite Hw.
  reflexivity.
  discriminate.
  apply and_from_or_not.
  apply or_from_impl_not.
  assert (Definable X (comp 2 NOT [f])).
  apply unit_comp_def.
  exact H.
  exact Hdef.
  apply (def_ext H1).
  unfold comp.
  intro v.
  destruct v as (c,(c0,w0)).
  destruct c,c0,w0; simpl.
  rewrite Hw.
  reflexivity.
  discriminate.
  symmetry; apply negb_sym.
  transitivity true.
  exact Hv.
  reflexivity.
  rewrite Hw.
  reflexivity.
  discriminate.
  rewrite Hw.
  reflexivity.
  discriminate.
  exact H.
  exact H.
  apply and_from_or_not.
  apply or_from_rimpl_not.
  assert (Definable X (comp 2 NOT [f])).
  apply unit_comp_def.
  exact H.
  exact Hdef.
  apply (def_ext H1).
  intro v.
  destruct v as (c,(c0,w0)).
  destruct c,c0,w0; unfold comp; simpl.
  rewrite Hw.
  reflexivity.
  discriminate.
  rewrite Hw.
  reflexivity.
  discriminate.
  symmetry; apply negb_sym.
  exact Hv.
  rewrite Hw.
  reflexivity.
  discriminate.
  exact H.
  exact H.
  apply and_from_or_not.
  assert (Definable X (comp 2 NOT [f])).
  apply unit_comp_def.
  exact H.
  exact Hdef.
  apply (def_ext H1).
  intro v.
  destruct v as (c,(c0,v0)).
  destruct c,c0,v0; unfold comp; simpl.
  rewrite Hw.
  reflexivity.
  discriminate.
  rewrite Hw.
  reflexivity.
  discriminate.
  rewrite Hw.
  reflexivity.
  discriminate.
  symmetry; apply negb_sym.
  exact Hv.
  exact H.
Qed.

Lemma FC_from_five(X : forall n:nat, conn n -> Prop) : 
  (non_fp_def X /\ non_tp_def X /\ non_monotone_def X/\ 
   non_selfdual_def X/\ non_counting_def X)
  -> FC X.
Proof.
  intro.
  destruct H as [H_fp [H_tp [H_mon [H_sd H_c]]]].
  apply and_not_func_complete.
  apply odd_and_def.
  apply NOT_defined.
  exact H_fp.
  exact H_tp.
  exact H_mon.
  apply odd_from_not_counting. 
  apply NOT_defined.
  exact H_fp.
  exact H_tp.
  exact H_mon.
  apply (def_ext (F_defined H_fp H_tp H_mon H_sd)).
  intro.
  auto.
  apply (def_ext (T_defined H_fp H_tp H_mon H_sd)).
  intro.
  auto.
  exact H_c.
  apply NOT_defined.
  exact H_fp.
  exact H_tp.
  exact H_mon.
Qed.

Definition non_fp(X : forall n:nat, conn n -> Prop) :=
  exists (n : nat)(f : conn n), X n f /\ ~f_preserving f.
Definition non_tp(X : forall n:nat, conn n -> Prop) :=
  exists (n : nat)(f : conn n), X n f /\ ~t_preserving f.
Definition non_mon(X : forall n:nat, conn n -> Prop) :=
  exists (n : nat)(f : conn n), X n f /\ ~monotone f.
Definition non_sd(X : forall n:nat, conn n -> Prop) :=
  exists (n : nat)(f : conn n), X n f /\ ~self_dual f.
Definition non_counting(X : forall n:nat, conn n -> Prop) :=
  exists (n : nat)(f : conn n), X n f /\ ~counting f.

Theorem Post_FC_Part_One(X : forall n:nat, conn n -> Prop) :
  (non_fp X /\ non_tp X /\ non_mon X /\ non_sd X /\ non_counting X)
   ->  FC X.
Proof.
  intro.
  destruct H as [ [n1 [f1 [X1 not_fp]]] H].
  destruct H as [ [n2 [f2 [X2 not_tp]]] H].
  destruct H as [ [n3 [f3 [X3 not_mon]]] H].
  destruct H as [ [n4 [f4 [X4 not_sd]]] H].
  destruct H as [n5 [f5 [X5 not_counting]]].
  apply FC_from_five.
  split.
  exists n1,f1.
  split.
  exact not_fp.
  apply atom_def.
  exact X1.
  split.
  exists n2,f2.
  split.
  exact not_tp.
  apply atom_def.
  exact X2.
  split.
  exists n3,f3.
  split.
  exact not_mon.
  apply atom_def.
  exact X3.
  split.
  exists n4,f4.
  split.
  exact not_sd.
  apply atom_def.
  exact X4.
  exists n5,f5.
  split.
  exact not_counting.
  apply atom_def.
  exact X5.
Qed.