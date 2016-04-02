Set Implicit Arguments.

Section vectors.

Variable (A : Set).

Fixpoint vec (n : nat) : Set :=
  match n with
  | 0    => unit
  | S m  => (A*(vec m))%type
  end.

Definition vhead (n : nat)(v : vec (S n)) : A :=
  match v with
  |(a,w) => a
  end.

Definition vtail (n : nat)(v : vec (S n)) : vec n :=
  match v with
  |(a,w) => w
  end.

Fixpoint const_vec (n : nat) (a : A) : vec n :=
  match n with
    0   => tt 
  | S m => (a,const_vec m a)
  end. 

Inductive empty : Type := .

Definition emptyf : empty -> A.
  intro.
  destruct H.
Qed.

Fixpoint fin (n : nat) : Set :=
  match n with 
    0   => empty
  | S n => (unit + fin n)%type
  end.

(*

Fixpoint rm_nth_vec (n : nat) : forall (m : nat), vec (n + S m) -> vec (n + m) :=
  match n as n return (forall m : nat, vec (n + S m) -> vec (n + m)) with
    0   => vtail
  | S n => fun m v => ((vhead v),(rm_nth_vec n m (vtail v)))
  end.

*)

Fixpoint item_at (n : nat) : fin n -> vec n -> A :=
  match n as n return fin n -> vec n -> A with
  |0   => fun i v => emptyf i
  |S m => fun i v => match i with
                     |inl tt => vhead v
                     |inr j  => item_at m j (vtail v)
                     end
  end.

Lemma vec_ext : forall (n : nat)(v w : vec n),
  (forall i : fin n, item_at n i v = item_at n i w) -> v = w.
Proof.
  induction n.
  intros.
  destruct v,w; reflexivity.
  intros.
  destruct v as [b v'], w as [c w'].
  assert (b = c).
  transitivity (item_at (S n) (inl tt) (b,v')).
  simpl; reflexivity.
  rewrite H.
  simpl; reflexivity.
  assert (v' = w').
  apply IHn.
  intro i.
  transitivity (item_at (S n) (inr i) (b , v')).
  simpl; reflexivity.
  rewrite H.
  simpl; reflexivity.
  rewrite H0, H1; reflexivity.
Qed.

Lemma const_vec_constant : forall (n : nat)(i : fin n)(a : A),
  item_at n i (const_vec n a) = a.
Proof.
  intros.
  induction n.
  destruct i.
  destruct i.
  destruct u.
  simpl; reflexivity.
  apply IHn.
Qed.

End vectors.

(* Notation borrowed from Coq.Lists.List *)

Notation " [ ] " := (tt : vec 0).
Notation " [ x ] " := ((x,tt) : vec 1).
Notation " [ x , .. , y ] " := (pair x .. (pair y tt) ..).

Fixpoint vec_ap (A B : Set) (n : nat) : vec (A -> B) n -> A -> vec B n :=
  match n as n return vec (A -> B) n -> A -> vec B n with
    0   => fun _ _ => (tt : vec B 0)
  | S m => fun fs a => ( ((vhead fs) a) , (vec_ap B m (vtail fs) a) )
  end.

Lemma vec_ap_lemma : forall (A B : Set)(n : nat)(i : fin n)(fs : vec (A -> B) n)(a : A),
  item_at B n i (vec_ap B n fs a) = (item_at (A -> B) n i fs) a.
Proof.
  intros A B.
  induction n.
  intro i; destruct i.
  intros.
  destruct fs as [f1 fs'].
  destruct i.
  destruct u.
  simpl.
  reflexivity.
  simpl.
  apply IHn.
Qed.

Lemma vec_ap_vtail_comm : forall (A B : Set)(n : nat)(fs : vec (A -> B) (S n))(a : A),
  vec_ap B n (vtail fs) a = vtail (vec_ap B (S n) fs a).
Proof.
  intros.
  auto.
Qed.

Fixpoint to_vec(n : nat)(A : Set) : (fin n -> A) -> vec A n :=
  match n as n return (fin n -> A) -> vec A n with
  |0     => fun f => (tt : vec A 0)
  |(S m) => fun f => ( f (inl tt) , to_vec m (fun j => f (inr j)) )
  end.

Lemma to_vec_correct : forall (n : nat)(A : Set)(f : fin n -> A)(i : fin n),
   item_at A n i (to_vec n f) = f i.
Proof.
  intro n.
  induction n.
  intros.
  destruct i.
  intros.
  destruct i.
  destruct u.
  simpl.
  reflexivity.
  simpl.
  rewrite IHn.
  reflexivity.
Qed.
