(* Alternating-Time Temporal Logic *)
Require Export List.
Require Export Classical.
Require Export Decidable.
Require Export FunctionalExtensionality.

Parameter State : Set.
Parameter Player : Set.
Parameter Observable : Set.
Parameter Move : Set.
Parameter beq_player : Player -> Player -> bool.


Definition move_vec (q: State) := forall (p:Player), Move.

Definition observation := State -> Observable.

Definition delta := forall (q:State), move_vec q -> State.

Record CGS : Set := mkRat
                      {
                        size: nat;
                        lp:list Player;
                        o:observation;
                        d:@delta
                       }.

(* TODO: consider limiting coalitions to lp. *)

Definition succ (g:CGS) (q q':State) := exists mv:move_vec q, q'=g.(d) q mv.

Fixpoint computation_property_fix (g:CGS) (l:list State) : Prop :=
  match l with
  | nil => False
  | x::l' => match hd_error l' with
             | None => True
             | Some y => @succ g x y /\ @computation_property_fix g l'
             end
  end.

Definition computation_property (g:CGS) (q:State) (l:list State) : Prop :=
  (hd_error l) = Some q /\ @computation_property_fix g l.

Definition computation (g:CGS) (q:State) : Set := {l:list State | @computation_property g q l}.

Theorem computation_property_suffix :
  forall (g:CGS) (l:list State) (q a b:State),
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
  forall (g:CGS) (q:State) (l0 l1: list State),
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
  forall (g:CGS) (n:nat) (q:State) (l:@computation g q),
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
           (g:CGS)
           (q:State)
           (l: computation g q)
           (n:nat)
           : computation g q
:=
  @exist (list State)
         (fun l => computation_property g q l)
         (firstn (S n) (proj1_sig l))
         (computation_property_prefix g n q l).

Check computation_prefix.

Definition strategy (g:CGS) (p:Player) : Set := forall (q:State) (l:computation g q), Move.

Definition coalition : Type := Player -> bool.

Definition coal_comp (c:coalition) : coalition := fun p:Player => negb (c p).

(* Definition grand (g:CGS) : coalition := g.(lp). *)
(* Definition nobody : coalition := nil. *)
(* Definition coal_comp (g:CGS) (c:coalition) : coalition := *)
(*   let x := fix fx (y z:coalition) *)
(*              := match y with *)
(*                 | nil => z *)
(*                 | a::y' => if existsb (beq_player a) c then fx y' z else fx y' (a::z) *)
(*                 end *)
(*   in x g.(lp) nil. *)

(* Definition coal_union (c1 c2 : coalition) : coalition := c1 ++ c2. *)

(*
Definition coal_intersection (c1 c2: coalition) : coalition :=
  let x := fix fx (y1 y2 z: coalition)
*)

Definition strategy_set (g:CGS) (c:coalition) : Set := forall (p:Player), c p = true -> strategy g p.

Definition outcomes (g:CGS) (q:State) (c:coalition) (ss:strategy_set g c) (l: computation g q) : Prop
:=
  forall (i:nat)
         (p:Player)
         (H: c p = true)
         (m:move_vec (nth i (proj1_sig l) q)),
    let x := computation_prefix g q l i in
    m p = ss p H q x ->
    S i  < (length (proj1_sig l)) ->
    g.(d) (nth i (proj1_sig l) q) m = (nth (i+1) (proj1_sig l) q).


Inductive sentence : Type :=
| obs : Observable -> sentence
| lnot : sentence -> sentence
| land : sentence -> sentence -> sentence
| lor : sentence -> sentence -> sentence
| possible_next : coalition -> sentence -> sentence
| possible_once : coalition -> sentence -> sentence
| possible_always : coalition -> sentence -> sentence
| possible_until : coalition -> sentence -> sentence -> sentence.


Notation "p //\\ q" := (land p q) (at level 30).
Notation "p \\// q" := (lor p q) (at level 30).
Notation "!! p" := (lnot p)  (at level 30).
Notation "p --> q" := (lnot (land (lnot p) q)) (at level 30).
Notation "<< c >>o p" := (possible_next c p) (at level 50).
Notation "<< c >>^ p" := (possible_once c  p) (at level 50).
Notation "<< c >># p" := (possible_always c p) (at level 50).
Notation "<< c >> p %% q" := (possible_until c p q) (at level 50).
Notation "[[ c ]]o p" := (possible_next (fun p0:Player => ~(c p0)) p) (at level 50).
Notation "[[ c ]]^ p" := (possible_once (coal_comp c) p) (at level 50).
Notation "[[ c ]]# p" := (possible_always (coal_comp c) p) (at level 50).
Notation "[[ c ]] p %% q" := (possible_until (coal_comp c) p  q) (at level 50).

Check forall  (g:CGS) (q:State) (c: coalition),
    exists (ss:strategy_set g c),
      forall (l:computation g q),
        outcomes g q c ss l.

Variable not_helper : CGS -> State -> sentence -> Prop.

Inductive verifiesI: CGS -> State -> sentence -> Prop :=
| verifiesObs: forall (g: CGS) (q: State) (a: Observable),
    g.(o) q = a -> verifiesI g q (obs a)
| verifiesNot: forall (g: CGS) (q: State) (phi: sentence),
    ~ not_helper g q phi ->
    verifiesI g q (!! phi)
| verifiesAnd: forall (g: CGS) (q: State) (phi1 phi2: sentence),
    verifiesI g q phi1 ->
    verifiesI g q phi2 ->
    verifiesI g q (phi1 //\\ phi2)
| verifiesPossibleNext: forall (g: CGS) (q: State) (phi: sentence) (c:coalition),
    (exists (ss:strategy_set g c),
      forall (l:computation g q),
        outcomes g q c ss l ->
        verifiesI g (nth 1 (proj1_sig l) q) phi) ->
    verifiesI g q (<<c>>o phi)
| verifiesPossibleOnce: forall (g: CGS) (q: State) (phi: sentence) (c:coalition),
    (exists (ss:strategy_set g c),
        forall (l:computation g q),
          outcomes g q c ss l ->
          (exists n:nat, verifiesI g (nth n (proj1_sig l) q) phi)) ->
    verifiesI g q (<<c>>^ phi)
| verifiesPossibleAlways: forall (g: CGS) (q: State) (phi: sentence) (c:coalition),
    (exists (ss:strategy_set g c),
        forall (l:computation g q),
          outcomes g q c ss l ->
          (forall n:nat, verifiesI g (nth n (proj1_sig l) q) phi)) ->
    verifiesI g q (<<c>>^ phi).
 

    
    
Fixpoint verifies (g:CGS) (q:State) (phi:sentence) :Prop :=
  match phi with
  | obs a => g.(o) q = a
  | !! a => ~ (verifies g q a)
  | a //\\ b => (verifies g q a) /\ (verifies g q b)
  | a \\// b => (verifies g q a) \/ (verifies g q b)
  | <<c>>o a => forall (l:computation g q),
      exists (ss:strategy_set g c),
        outcomes g q c ss l ->
        (verifies g (nth 1 (proj1_sig l) q) a)
  | <<c>>^ a => forall (l:computation g q),
      exists (n:nat) (ss:strategy_set g c),
        outcomes g q c ss l ->
        (verifies g (nth n (proj1_sig l) q) a)
  | <<c>># a => forall (l:computation g q) (n:nat),
      exists (ss:strategy_set g c),
        outcomes g q c ss l ->
        (verifies g (nth n (proj1_sig l) q) a)
  | <<c>> a %% b => forall (l:computation g q),
      exists (n:nat) (ss:strategy_set g c),
        outcomes g q c ss l ->
        ((verifies g (nth n (proj1_sig l) q) b)
        /\ forall (m:nat),
            m < n -> (verifies g (nth m (proj1_sig l) q) a))
  end.

Definition invariant (g1 g2:CGS) : Prop := forall (phi:sentence) (q:State),
    verifies g1 q phi <-> verifies g2 q phi.
    
(* TODO: invariance. *)
(* TODO: proof calculus *)

Definition spec : Type := sentence -> Prop.

Definition g_in_spec (sp:spec) (g:CGS) (q:State) : Prop := forall (phi:sentence), sp phi -> verifies g q phi.

Theorem coal_comp_comp : forall c, coal_comp (coal_comp c) = c.
Proof.
  intros.
  unfold coal_comp. intros. apply functional_extensionality. intros. destruct (c x).
  - reflexivity.
  - reflexivity.
Qed.

Theorem lnot_lnot : forall g q phi, verifies g q (!! (!! phi)) -> verifies g q phi.
Proof.
  simpl. intros. apply NNPP. apply H.
Qed.
  
Axiom d_sentence : forall (g:CGS) (q:State) (phi:sentence), decidable (verifies g q phi).

Theorem coalition_complement_once_always : forall (g:CGS) (q:State) (phi:sentence) (c:coalition),
    verifies g q  (<<c>>^ phi) <-> verifies g q (!! ([[c]]# (!! phi))).
Proof.
  intros g q.
  assert (F: forall c phi, verifies g q (<<c>>^ phi) -> verifies g q (!! ([[c]]# ( !! phi)))).
  { simpl. intros.
    apply ex_not_not_all.
    
    assert (P: computation_property g q (q::nil)).
    {
      unfold computation_property. split. 
      - reflexivity.
      - reflexivity.
    }
    pose (l := (exist (computation_property g q) (q::nil) P) : (computation g q)).
    exists l.
    apply ex_not_not_all.
    exists 0.
    apply all_not_not_ex.
    unfold not. intros.
    apply H0.
    unfold outcomes. intros. simpl in H3. destruct i.
    + simpl in H3. inversion H3. inversion H5.
    + inversion H3. inversion H5.
    + simpl. destruct (H l). induction x.
      * destruct H1. apply H1. unfold outcomes. intros. inversion H4. inversion H6.
      * apply IHx. destruct H1. exists x0. intros. apply H1 in H2.
        assert (proj1_sig l = (q::nil)).
        {
          unfold proj1_sig. unfold l. reflexivity.
        }
        assert (forall m:nat, nth (S m) (proj1_sig l) q = nth m (proj1_sig l) q).
        {
          intros. induction m.
          - reflexivity.
          - symmetry. apply nth_overflow. simpl. assert (forall m, 1 <= S m).
            {
              intros. induction m0.
              - reflexivity.
              - apply le_S. apply IHm0.
            }
            apply H4.
        }
        rewrite H4 in H2. apply H2.
  }
  assert (B: forall c phi, verifies g q (!! ([[c]]# (!! phi))) -> verifies g q (<<c>>^ phi)).
  {
    simpl. intros.
    apply not_all_ex_not in H. destruct H.
    apply not_all_ex_not in H. destruct H.
    unfold not in H.
    exists x0. 
  }