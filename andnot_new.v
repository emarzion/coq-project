Set Implicit Arguments.

Require Import Coq.Bool.Bool.
Require Import vecs_new.

Definition bool_le (x y : bool) : Prop :=
  match x with
    false => True
  | true => match y with 
      false => False 
    | true => True
    end
  end.

Fixpoint vec_le (n : nat) : vec bool n -> vec bool n -> Prop :=
  match n as n return vec bool n -> vec bool n -> Prop with
    0   => fun _ _ => True
  | S m => fun v w => bool_le (vhead v) (vhead w) /\ vec_le m (vtail v) (vtail w)
  end.

Lemma vec_le_correct (n : nat)(v w : vec bool n) :
  vec_le n v w -> forall i : fin n,
    bool_le (item_at bool n i v) (item_at bool n i w).
Proof.
  intros.
  induction n.
  destruct i.
  destruct v,w,i.
  destruct b,b0,u.
  simpl.
  reflexivity.
  simpl in H.
  destruct H.
  contradiction.
  simpl.
  reflexivity.
  simpl.
  reflexivity.
  simpl.
  simpl in H.
  apply IHn.
  apply H.
Qed.   

Fixpoint index_eqb (n : nat) : fin n -> fin n -> bool :=
  match n as n return fin n -> fin n -> bool with
    0   => fun e e' => emptyf bool e
  | S n => fun i j =>
    match i , j with
      inl tt , inl tt => true
    | inl tt , inr l  => false
    | inr k  , inl tt => false
    | inr k  , inr l  => index_eqb n k l
    end
  end.

Definition conn (k : nat) :=
  vec bool k -> bool.

Definition conn_ext_eq (n : nat) (f g : conn n) :=
  forall v , f v = g v.

Notation "f [=] g" := (conn_ext_eq f g) (at level 38, right associativity).

Definition comp (n k : nat) (f : conn n) (gs : vec (conn k) n) : conn k :=
  fun xs => f (vec_ap bool n gs xs).
(*
Definition remove_component (n m : nat) (f : conn (n + m)) : conn (n + S m) :=
  fun x => f (rm_nth_vec Bool n m x).
*)
Definition ID  : conn 1 :=
  fun v => match v with
           |[ b ] => b
           end.

Definition NOT : conn 1 :=
  fun v => match v with
           |[ b ] => negb b
           end.

Definition AND : conn 2 :=
  fun v => match v with
           |[ b1 , b2 ] => andb b1 b2
           end.

Definition OR : conn 2 :=
  fun v => match v with
           |[ b1 , b2 ] => orb b1 b2
           end.

Definition IMPL : conn 2 :=
  fun v => match v with
           |[ b1 , b2 ] => implb b1 b2
           end.

Definition rIMPL : conn 2 :=
  fun v => match v with
           |[ b1 , b2 ] => match b1,b2 with
                           |false , false => true
                           |false , true  => false
                           |true  , false => true
                           |true  , true  => true
                           end
           end.

Definition const (k : nat)(x : bool) : conn k :=
  fun v => x.

Definition proj (n : nat) (i : fin n) : conn n :=
  fun v : vec bool n => item_at bool n i v .

Definition p1 : conn 2 := 
  proj 2 (inl tt).

Definition p2 : conn 2 := 
  proj 2 (inr (inl tt)).

(* Definition of definable from a set X of connectives *)
Inductive Definable(X : forall n:nat, conn n -> Prop) : forall k, conn k -> Prop :=
  | atom_def : forall (n : nat)(f : conn n), X n f -> Definable X f
  | null_def : forall x : bool, Definable X (const 1 x) -> Definable X (const 0 x)
  | project  : forall (n : nat) (i : fin n), Definable X (proj n i)
  | compose  : forall (n k : nat) (f : conn n) (gs : vec (conn k) n),
               Definable X f -> (forall i : fin n, Definable X (item_at (conn k) n i gs)) -> Definable X (comp k f gs)
  | def_ext  : forall (n : nat) (f g : conn n), Definable X f -> f [=] g -> Definable X g.

(*functionally complete*)
Definition FC(X : forall n:nat, conn n -> Prop) :=
  (forall (n : nat)(f : conn n), Definable X f).

Definition DeM_or := 
  comp 2 NOT [ comp 2 AND [ comp 2 NOT [ p1 ] , comp 2 NOT [ p2 ] ] ].

Lemma or_def : DeM_or [=] OR.
Proof.
  unfold DeM_or.
  unfold comp.
  intros v.
  destruct v as [b1 [b2 u]].
  destruct b1, b2, u; simpl; reflexivity.
Qed.

(* two lemmas which make the compose rule easier to use *)
Lemma unit_comp_def(X : forall n:nat, conn n -> Prop) : forall k, forall f : conn 1, forall g : conn k,
  Definable X f -> Definable X g -> Definable X (comp k f [ g ]).
Proof.
  intros.
  apply compose.
  exact H.
  intro.
  destruct i.
  destruct u.
  simpl.
  exact H0.
  destruct f0.
Qed.

Lemma bin_comp_def(X : forall n:nat, conn n -> Prop) : forall k, forall f : conn 2 , forall g1 g2 : conn k,
  Definable X f -> Definable X g1 -> Definable X g2 -> Definable X (comp k f [g1 , g2]).
Proof.
  intros.
  apply compose.
  exact H.
  destruct i.
  destruct u.
  simpl.
  exact H0.
  destruct f0.
  destruct u.
  simpl.
  exact H1.
  destruct f0.
Qed.

Lemma id_proj : proj 1 (inl tt) [=] ID.
Proof.
  unfold ID, proj.
  intro v.
  destruct v as [b u].
  destruct b,u; simpl; reflexivity.
Qed.

Lemma id_def(X : forall n:nat, conn n -> Prop) : Definable X ID.
Proof.
  assert (Definable X (proj 1 (inl tt))).
  apply project.
  apply (def_ext H).
  exact id_proj.
Qed.

Lemma or_from_and_not(X : forall n:nat, conn n -> Prop) : Definable X AND -> Definable X NOT -> Definable X OR.
Proof.
  intros.
  assert (Definable X DeM_or).
  apply unit_comp_def.
  exact H0.
  apply bin_comp_def.
  exact H.
  apply unit_comp_def.
  exact H0.
  apply project.
  apply unit_comp_def.
  exact H0.
  apply project.
  apply (def_ext H1).
  apply or_def.
Qed.

Definition DeM_and := 
  comp 2 NOT [ comp 2 OR [ comp 2 NOT [ p1 ] , comp 2 NOT [ p2 ] ] ].

Lemma and_DeM_def : DeM_and [=] AND.
Proof.
  unfold DeM_and.
  unfold comp.
  intros v.
  destruct v as [b1 [b2 u]].
  destruct b1, b2, u; simpl; reflexivity.
Qed.  

Lemma and_from_or_not(X : forall n:nat, conn n -> Prop) : Definable X OR -> Definable X NOT -> Definable X AND.
Proof.
  intros.
  assert (Definable X DeM_and).
  apply unit_comp_def.
  exact H0.
  apply bin_comp_def.
  exact H.
  apply unit_comp_def.
  exact H0.
  apply project.
  apply unit_comp_def.
  exact H0.
  apply project.
  apply (def_ext H1).
  apply and_DeM_def.
Qed.

Definition DS_or :=
  comp 2 IMPL [comp 2 NOT [ p1 ] , p2].

Lemma or_DS_def : DS_or [=] OR.
Proof.
  unfold DS_or.
  unfold comp.
  intros v.
  destruct v as [b1 [b2 u]].
  destruct b1, b2, u; simpl; reflexivity.
Qed.

Lemma or_from_impl_not(X : forall n:nat, conn n -> Prop) : Definable X IMPL -> Definable X NOT -> Definable X OR.
Proof.
  intros.
  assert (Definable X DS_or).
  apply bin_comp_def.
  exact H.
  apply unit_comp_def.
  exact H0.
  apply project.
  apply project.
  apply (def_ext H1).
  apply or_DS_def.
Qed.

Definition rDS_or :=
  comp 2 rIMPL [p1 , comp 2 NOT [ p2 ]].

Lemma or_rDS_def : rDS_or [=] OR.
Proof.
  unfold rDS_or.
  unfold comp.
  intros v.
  destruct v as [b1 [b2 u]].
  destruct b1, b2, u; simpl; reflexivity.
Qed.

Lemma or_from_rimpl_not(X : forall n:nat, conn n -> Prop) : Definable X rIMPL -> Definable X NOT -> Definable X OR.
Proof.
  intros.
  assert (Definable X rDS_or).
  apply bin_comp_def.
  exact H.
  apply project.
  apply unit_comp_def.
  exact H0.
  apply project.
  apply (def_ext H1).
  apply or_rDS_def.
Qed.

Definition NonCon_F := comp 1 AND [ ID , NOT ].

Lemma f_def : NonCon_F [=] (const 1 false).
Proof.
  unfold NonCon_F.
  unfold comp.
  intro v.
  destruct v as [b u].
  destruct b, u; simpl; reflexivity.  
Qed.

Lemma f_from_and_not(X : forall n:nat, conn n -> Prop) : Definable X AND -> Definable X NOT -> Definable X (const 1 false).
Proof.
  intros.
  assert (Definable X NonCon_F).
  apply bin_comp_def.
  exact H.
  apply id_def.
  exact H0.
  apply (def_ext H1).
  apply f_def.
Qed.

Definition LEM_T := comp 1 OR [ID , NOT].

Lemma t_def : LEM_T [=] (const 1 true).
Proof.
  unfold LEM_T.
  unfold comp.
  intro v.
  destruct v as [b u].
  destruct b,u; simpl; reflexivity.
Qed.

Lemma t_from_and_not(X : forall n:nat, conn n -> Prop) : Definable X AND -> Definable X NOT -> Definable X (const 1 true).
Proof.
  intros.
  assert (Definable X LEM_T).
  apply bin_comp_def.
  apply or_from_and_not.
  exact H.
  exact H0.
  apply id_def.
  exact H0.
  apply (def_ext H1).
  apply t_def.
Qed.

Lemma nullconn_is_constant : forall f : conn 0, (const 0 false) [=] f \/ (const 0 true) [=] f.
Proof.
  intro f.
  assert (f tt = false \/ f tt = true).
  destruct (f tt).
  right; reflexivity.
  left; reflexivity.
  destruct H.
  left.
  intro.
  destruct v.
  rewrite H; simpl; reflexivity.
  right.
  intro.
  destruct v.
  rewrite H; simpl; reflexivity.
Qed.

Lemma all_nullconn_from_and_not(X : forall n:nat, conn n -> Prop) : Definable X AND -> Definable X NOT -> 
  (forall f:conn 0, Definable X f).
Proof.
  intros.
  destruct (nullconn_is_constant f).
  assert (Definable X (const 0 false)).
  apply null_def.
  apply f_from_and_not.
  exact H.
  exact H0.
  apply (def_ext H2).
  exact H1.
  assert (Definable X (const 0 true)).
  apply null_def.
  apply t_from_and_not.
  exact H.
  exact H0.
  apply (def_ext H2).
  exact H1.
Qed.

Lemma ext_unit_subst : forall (n : nat)(f : conn 1)(g h : conn n),
  g [=] h -> comp n f [ g ] [=] comp n f [ h ].
Proof.
  intros.
  intro v.
  unfold comp.
  simpl.
  rewrite H.
  reflexivity.
Qed.

Lemma ext_bin_subst : forall (n : nat)(f : conn 2)(g1 g2 h1 h2 : conn n),
  g1 [=] h1 -> g2 [=] h2 -> comp n f [ g1 , g2 ] [=] comp n f [ h1 , h2 ].
Proof.
  intros.
  intro v.
  unfold comp.
  simpl.
  rewrite H, H0.
  reflexivity.
Qed.

(* some lemmas for simplifying expressions with AND and OR *)

Lemma and_left_f : forall (n:nat)(g h : conn n)(v : vec bool n),
  g v = false -> comp n AND [g , h] v = false.
Proof.
  intros.
  unfold comp.
  simpl.
  rewrite H.
  apply andb_false_l.
Qed.

Lemma and_left_t : forall (n:nat)(g h : conn n)(v : vec bool n),
  g v = true -> comp n AND [g , h] v = h v.
Proof.
  intros.
  unfold comp.
  simpl.
  rewrite H.
  apply andb_true_l.
Qed.

Lemma or_left_f : forall (n:nat)(g h : conn n)(v : vec bool n),
  g v = false -> comp n OR [g , h] v = h v.
Proof.
  intros.
  unfold comp.
  simpl.
  rewrite H.
  apply orb_false_l.
Qed.

Lemma or_left_t : forall (n:nat)(g h : conn n)(v : vec bool n),
  g v = true -> comp n OR [g , h] v = true.
Proof.
  intros.
  unfold comp.
  simpl.
  rewrite H.
  apply orb_true_l.
Qed.

Lemma or_right_f : forall (n:nat)(g h : conn n)(v : vec bool n),
  h v = false -> comp n OR [g , h] v = g v.
Proof.
  intros.
  unfold comp.
  simpl.
  rewrite H.
  apply orb_false_r.
Qed.

Lemma or_right_t : forall (n:nat)(g h : conn n)(v : vec bool n),
  h v = true -> comp n OR [g , h] v = true.
Proof.
  intros.
  unfold comp.
  simpl.
  rewrite H.
  apply orb_true_r.
Qed.

Definition change_first_arg (n : nat) (f : conn (S n)) (x : bool) : conn (S n) :=
  fun v => f (x,(vtail v)).

(*
Lemma remove_eq (n : nat)(f : conn (S n))(x : bool) : 
  remove_component 0 n (fun v => f (x,v)) [=] (remove_first_arg f x).
Proof.
  intro v.
  simpl v; destruct v.
  simpl.
  unfold remove_component.
  unfold remove_first_arg.
  simpl.
  unfold vcons; reflexivity.
Qed.
*)
(* the idea: fun x,ybar => (x /\ (f T,ybar)) \/ (~x /\ (f F,ybar)) *) 

Definition and_or_not_form (n : nat) (f : conn (S n)) : conn (S n) :=
  comp (S n) OR 
    [ 
      (comp (S n) AND [ (proj (S n) (inl tt)) , (change_first_arg f true) ] ) , 
      (comp (S n) AND [ comp (S n) NOT [ proj (S n) (inl tt)] , change_first_arg f false ] )
    ].

Lemma first_proj_lemma : forall (n : nat)(x : bool)(v : vec bool n), proj (S n) (inl tt) (x,v) = x.
Proof.
  intros.
  unfold proj.
  simpl.
  reflexivity.
Qed.

Lemma un_comp_lemma : forall (n : nat)(f : conn 1)(g : conn (S n))(v : vec bool (S n)),
  comp (S n) f [ g ] v = f ( [ g v ] ).
Proof.
  intros.
  unfold comp.
  simpl.
  reflexivity.
Qed.

Lemma and_or_not_eq : forall (n : nat)(f : conn (S n)), and_or_not_form f [=] f.
Proof.
  intros n f v.
  destruct v.
  unfold and_or_not_form.
  unfold comp.
  unfold change_first_arg.
  destruct b.
  simpl.
  apply orb_false_r.
  simpl.
  reflexivity.
Qed.

Definition proj_vec(n : nat) : vec (conn n) n := to_vec n (fun i => proj n i).

Lemma proj_vec_correct : forall (n : nat)(v : vec bool n), vec_ap bool n (proj_vec n) v = v.
Proof.
  intros.
  unfold proj_vec.
  apply vec_ext.
  intro i.
  rewrite vec_ap_lemma.
  rewrite to_vec_correct.
  unfold proj.
  reflexivity.
Qed.

Lemma ignore_first_proj_def : forall (n : nat)(g : conn n),
  comp (S n) g (vtail (proj_vec (S n))) [=] (fun v => g (vtail v)).
Proof.
  intros.
  intro v.
  unfold comp.
  f_equal.
  rewrite vec_ap_vtail_comm.
  f_equal.
  apply proj_vec_correct.
Qed.

Lemma ignore_first_definable(X : forall n:nat, conn n -> Prop) :  forall (n : nat)(f : conn (S n)),
  (exists g : conn n, Definable X g /\  (fun v => g (vtail v)) [=] f) -> Definable X f.
Proof.
  intros.
  destruct H as [g [gDef Hfg]].
  assert (Definable X (fun v => g (vtail v))).
  assert (Definable X (comp (S n) g (vtail (proj_vec (S n))))).
  apply compose.
  exact gDef.
  intro i.
  simpl.
  rewrite to_vec_correct.
  apply project.
  apply (def_ext H).
  intro v.
  apply ignore_first_proj_def.
  apply (def_ext H).
  exact Hfg.
Qed.  

Lemma and_not_func_complete(X : forall n:nat, conn n -> Prop) : Definable X AND -> Definable X NOT ->
  FC X.
Proof.
  intros.
  induction n.
  apply all_nullconn_from_and_not.
  exact H.
  exact H0.
  intro f.
  assert (Definable X (and_or_not_form f)).
  apply bin_comp_def.
  apply or_from_and_not.
  exact H.
  exact H0.
  apply bin_comp_def.
  exact H.
  apply project.
  apply ignore_first_definable.
  exists (fun v => f (true,v)).
  split.
  apply IHn.
  intro v.
  unfold change_first_arg.
  reflexivity.
  apply compose.
  exact H.
  intro i; destruct i.
  destruct u.
  simpl.
  apply compose.
  exact H0.
  intro i; destruct i.
  destruct u.
  simpl.
  apply project.
  destruct f0.
  destruct f0.
  destruct u.
  simpl.
  apply ignore_first_definable.
  exists (fun v => f (false,v)).
  split.
  apply IHn.
  intro v.
  unfold change_first_arg; reflexivity.
  destruct f0.
  apply (def_ext H1).
  apply and_or_not_eq.
Qed.