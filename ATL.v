(* Alternating-Time Temporal Logic *)
Require Export List.

Parameter State : Set.
Parameter Player : Set.
Parameter Observable : Set.


Definition move_number : Set := State -> Player -> nat.

Definition move {m:move_number} (q:State) (p:Player) :Set := nat.

Definition move_vec {m:move_number} (q: State)  := forall (p:Player), @move m q p.

Definition observation := State -> Observable.

Definition delta {m:move_number} := forall (q:State), @move_vec m q -> State.

Record CGS : Set := mkRat
                      {
                        size: nat;
                        lp:list Player;
                        m:move_number;
                        o:observation;
                        d:@delta m
                       }.

(* TODO: consider limiting coalitions to lp. *)

Definition succ {g:CGS} (q q':State) := exists mv:@move_vec g.(m) q, q'=g.(d) q mv.

Fixpoint computation_property_fix {g:CGS} (l:list State) : Prop :=
  match l with
  | nil => False
  | x::l' => match hd_error l' with
             | None => True
             | Some y => @succ g x y /\ @computation_property_fix g l'
             end
  end.

Definition computation_property {g:CGS} (q:State) (l:list State) : Prop :=
  (hd_error l) = Some q /\ @computation_property_fix g l.

Definition computation {g:CGS} (q:State) : Set := {l:list State | @computation_property g q l}.

Theorem computation_property_suffix :
  forall {g:CGS} (l:list State) (q a b:State),
    @computation_property g q (b::l) /\ @succ g a b -> @computation_property g a (a::b::l).
Proof.
  intros. destruct H. destruct H. unfold computation_property. split.
  - reflexivity.
  - simpl. split.
    + apply H0.
    + simpl in H1. apply H1.
Qed.

Theorem  length_hd_error : forall (A:Type) (l:list A), 1 <= length l <-> exists y:A, hd_error l = Some y.
Proof.
intros. split.
- induction l.
  + intros. inversion H.
  + intros. exists a. reflexivity.
- intros. destruct H. assert (x::(tl l) = l).
  { symmetry. apply hd_error_tl_repr. split.
    - apply H.
    - reflexivity.
  }
  rewrite <- H0. simpl. induction (length (tl l)).
  + reflexivity.
  + apply le_S. apply IHn.
Qed.

Theorem hd_error_app : forall (b0 b1: list State) (a:State), hd_error b0 = Some a -> (hd_error (b0 ++ b1)) = Some a.
  {
    intros. induction b0.
    - inversion H.
    - simpl. simpl in H. apply H.
  }
Qed.

Theorem computation_property_app :
  forall {g:CGS} (q:State) (l0 l1: list State),
    (1 <= (length l0)) -> @computation_property g q (l0 ++ l1) -> @computation_property g q l0.
Proof.
  intros. destruct H0. unfold computation_property. generalize dependent q. induction l0.
  - intros. inversion H.
  - intros. split.
    + simpl in H0. simpl. apply H0.
    + simpl. simpl in H1. simpl in H0. inversion H.
      *
        assert (hd_error l0 = None).
        {
          symmetry in H3. apply length_zero_iff_nil in H3.
          rewrite H3. reflexivity.
        }
        rewrite H2. apply I.
      * 
        assert (length l0 > 0).
        { unfold gt. unfold lt. apply H3. }
        apply length_hd_error in H3. destruct H3. apply (hd_error_app l0 l1 x) in H3.
        rewrite H3 in H1. destruct H1. apply (IHl0 H4 H5 x) in H3.
        destruct H3.
        rewrite H3. split.
        -- apply H1.
        -- apply H6.
Qed.

  
Theorem computation_property_prefix :
  forall {g:CGS} (n:nat) (q:State) (l:@computation g q),
    @computation_property g q (firstn (S n) (proj1_sig l)).
Proof.
  intros. destruct l. unfold proj1_sig. destruct c.
  pose proof (hd_error_app (firstn (S n) x) (skipn (S n) x) q) as H1.
  assert ((hd_error (firstn (S n) x)) = Some q).
  {
    simpl. destruct x.
    - apply H.
    - simpl. simpl in H. apply H.
  }
  apply H1 in H2.
  destruct (length_hd_error State x).
  assert (exists y, hd_error x = Some y).
  { exists q. apply H. }
  apply H4 in H5.
  pose proof (@computation_property_app g q (firstn (S n) x) (skipn (S n) x)).
  assert (1 <= length (firstn (S n) x)).
  {
    induction x.
    - inversion H.
    - simpl. induction (firstn n x).
      + reflexivity.
      + simpl. apply le_S. apply IHl.
  }
  assert (@computation_property g q x).
  {
    unfold computation_property. split.
    - apply H.
    - apply H0.
  }
  rewrite firstn_skipn in H6.
  apply (H6 H7 H8).
Qed.
    
Definition computation_prefix
           {g:CGS}
           (q:State)
           (l: computation q)
           (n:nat)
           : computation q
:=
  @exist (list State)
         (fun l => @computation_property g q l)
         (firstn (S n) (proj1_sig l))
         (@computation_property_prefix g n q l).

Check computation_prefix.

Definition strategy {g:CGS} (p:Player) : Type := forall (q:State) (l:@computation g q), (@move g.(m) (last (proj1_sig l) q) p).

Definition coalition : Type := Player -> Prop.

Definition strategy_set {g:CGS} (c:coalition) : Type := forall (p:Player), c p -> @strategy g p.

Definition outcomes {g:CGS} (q:State) (c:coalition) (ss:strategy_set c) (l: computation q)
:=
  forall (i:nat)
         (p:Player)
         (H: c p)
         (m:move_vec (last (proj1_sig (computation_prefix q l i)) q)),
    let x := computation_prefix q l i in
    m p = ss p H q x
    -> g.(d) (last (proj1_sig x) q) m = (last (proj1_sig x) q).


Inductive sentence : Type :=
| obs : Observable -> sentence
| lnot : sentence -> sentence
| land : sentence -> sentence -> sentence
| possible_next : coalition -> sentence -> sentence
| possible_once : coalition -> sentence -> sentence
| possible_always : coalition -> sentence -> sentence
| possible_until : coalition -> sentence -> sentence -> sentence.


Notation "p //\\ q" := (land p q) (at level 30).
Notation "!! p" := (lnot p)  (at level 30).
Notation "p --> q" := (lnot (land (lnot p) q)) (at level 30).
Notation "<< c >>o p" := (possible_next c p) (at level 50).
Notation "<< c >>^ p" := (possible_once c  p) (at level 50).
Notation "<< c >># p" := (possible_always c p) (at level 50).
Notation "<< c >> p %% q" := (possible_until c p q) (at level 50).
Notation "[[ c ]]o p" := (lnot (possible_next c (lnot p))) (at level 50).
Notation "[[ c ]]<> p" := (lnot (possible_always c (lnot p))) (at level 50).
Notation "[[ c ]]# p" := (lnot (possible_always c (lnot p))) (at level 50).
Notation "[[ c ]] p %% q" := (lnot (possible_until c p (lnot q))) (at level 50).

Check forall (q:State) (c: coalition),
    exists (ss:strategy_set c),
      forall (l:computation q),
        outcomes q c ss l.

Fixpoint verifies {g:CGS} (q:State) (phi:sentence) :Prop :=
  match phi with
  | obs a => g.(o) q = a
  | !! a => ~ (@verifies g q a)
  | a //\\ b => (@verifies g q a) /\ (@verifies g q b)
  | <<c>>o a => exists (ss:strategy_set c),
                forall (l:computation q),
                  @outcomes g q c ss l
                  /\ (@verifies g (nth 1 (proj1_sig l) q) a)
  | <<c>>^ a => exists (ss:strategy_set c),
                forall (l:computation q),
                  @outcomes g q c ss l
                  /\ exists (n:nat),
                    (@verifies g (nth n (proj1_sig l) q) a)
  | <<c>># a => exists (ss:strategy_set c),
                forall (l:computation q) (n:nat),
                  @outcomes g q c ss l
                  /\ (@verifies g (nth n (proj1_sig l) q) a)
  | <<c>> a %% b => exists (ss:strategy_set c) (n:nat),
                  forall (l:computation q),
                    @outcomes g q c ss l
                    /\ (@verifies g (nth n (proj1_sig l) q) b)
                    /\ forall (m:nat),
                        m < n -> (@verifies g (nth m (proj1_sig l) q) a)
  end.

Definition invariant (g1 g2:CGS) : Prop := forall (phi:sentence) (q:State),
    @verifies g1 q phi <-> @verifies g2 q phi.
    
(* TODO: invariance. *)
(* TODO: proof calculus *)

Definition spec : Type := sentence -> Prop.