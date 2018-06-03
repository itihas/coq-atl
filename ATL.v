(* Alternating-Time Temporal Logic *)
Require Export List.
Require Export Classical.
Require Export Decidable.
Require Export FunctionalExtensionality.

Require Import Coq.Lists.List Coq.Bool.Bool.

Import Coq.Lists.List.ListNotations.

Scheme Equality for list.

Parameter State : Set.
Parameter Player : Set.
Parameter Observable : Set.     (* set of atomic truths that can hold at a given state. *)
Parameter Move : Set.           (* alphabet of moves individual players can make. 
*)
Parameter beq_state : State -> State -> bool.
Parameter beq_player : Player -> Player -> bool.

(* type corresponding to the set of moves each player makes. *)
Definition move_vec (q: State) := forall (p:Player), Move.

(* AHK says not all moves are available at all states. We express this using a function type [enabled], expressing which moves are available at which state.  *)
Definition enabled := State -> Player -> Move -> bool.

(* labeling function type. *)
Definition observation := State -> Observable.

(* transition function. *)
Definition delta := forall (q:State), move_vec q -> State.

Record CGS : Set := mkRat
                      {
                        size: nat;
                        lp:list Player;
                        e:enabled;
                        o:observation;
                        d:delta
                       }.

(* TODO: consider limiting coalitions to lp. *)

(* property of states [q] and [q'], expressind whether [q'] can be reached from [q] in game [g], under [g]'s transition function.*)
Definition succ (g:CGS) (q q':State) :=
  exists mv:move_vec q,
    (forall (p:Player),
        (g.(e) q p (mv p)) = true) /\
    q'=g.(d) q mv.

(* Computations are nonempty sequences of states [l] where every [l_(i+1)] is a successor of [l_i]. *)

(* [computation_property_fix] checks that successive states are successors according to the above property. *)
Fixpoint computation_property_fix (g:CGS) (l:list State) : Prop :=
  match l with
  | nil => False
  | x::l' => match hd_error l' with
             | None => True
             | Some y => succ g x y /\ computation_property_fix g l'
             end
  end.

(* A q-computation starts with state [q]. [computation_property] checks for this, and for [computation_property_fix] to hold.*)
Definition computation_property (g:CGS) (q:State) (l:list State) : Prop :=
  (hd_error l) = Some q /\ computation_property_fix g l.

(* Subset type of [list State] where [computation_property] holds. *)
Definition computation (g:CGS) (q:State) : Set := {l:list State | @computation_property g q l}.

(* If a [list State] is a [q]-computation, that same [list State] cons'ed with State [a] is an [a]-computation. *)
Theorem computation_property_cons :
  forall (g:CGS) (l:list State) (q a b:State),
    computation_property g q (b::l) /\ succ g a b -> computation_property g a (a::b::l).
Proof.
  intros. destruct H. destruct H. unfold computation_property. split.
  - reflexivity.
  - simpl. split.
    + apply H0.
    + simpl in H1. apply H1.
Qed.

(* A list has length > 0 iff there exists a head to the list.*)
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

(* The head of a list [b0++b1] is the head of list [b0] if [b0] is nonempty.*)
Theorem hd_error_app : forall (b0 b1: list State) (a:State), hd_error b0 = Some a -> (hd_error (b0 ++ b1)) = Some a.
  {
    intros. induction b0.
    - inversion H.
    - simpl. simpl in H. apply H.
  }
Qed.

(* If [computation_property] holds for [l0++l1] and [l0] is nonempty, [computation_property] holds for [l0]. *)
Theorem computation_property_app :
  forall (g:CGS) (q:State) (l0 l1: list State),
    (1 <= (length l0)) -> computation_property g q (l0 ++ l1) -> computation_property g q l0.
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

(* The nonempty prefix of a [q]-computation is a [q]-computation. *)
Theorem computation_property_prefix :
  forall (g:CGS) (n:nat) (q:State) (l:computation g q),
    computation_property g q (firstn (S n) (proj1_sig l)).
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

(* A function generating the [n+1]-long prefix of a [q]-computation.*)
Definition computation_prefix
           (g:CGS)
           (q:State)
           (l: computation g q)
           (n:nat)
           : computation g q
:=
  @exist (list State)
         (computation_property g q)(* (fun l => computation_property g q l) *)
         (firstn (S n) (proj1_sig l))
         (computation_property_prefix g n q l).

Check computation_prefix.


(* There is always a move available called [nothing], which if performed by every player fails to change state. *)
Parameter nothing: Move.
Axiom nothing_always_enabled : forall (g:CGS) (q:State) (p:Player), g.(e) q p nothing = true.
Axiom nothing_does_nothing : forall (g:CGS) (q:State), g.(d) q (fun _ => nothing) = q.


(* A strategy is a function from computations to moves, representing what a player would do in a particular play-through. *)
Definition strategy (g:CGS) (p:Player) : Set := forall (q:State) (l:computation g q), {m:Move | g.(e) q p m = true}.

Definition strat_nothing (g: CGS) (p:Player) : strategy g p :=
  fun q _ => exist (fun m => g.(e) q p m = true) nothing (nothing_always_enabled g q p).

(* A coalition is a set of players. *)
Definition coalition : Set := Player -> bool.

(* Coalition complement. *)
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

(* [strategy_set] is a type representing unique strategies only of members in the coalition. *)
Definition strategy_set (g:CGS) (c:coalition) : Set := forall (p:Player), c p = true -> strategy g p.

(* Whether a particular move vector obeys a given strategy set. *)
Definition strategy_set_enabled (g:CGS) (c:coalition) (ss:strategy_set g c) (q:State) (l:computation g q) (mv:move_vec q) :=
  forall (p:Player) (H:c p = true),
    mv p = proj1_sig (ss p H q l).
  
(* Strategy set where members of the coalition do nothing. *)
Definition ss_nothing (g:CGS) (c:coalition) : strategy_set g c := fun p _ => strat_nothing g p.



(* Property checking whether a given computation obeys a strategy set in all successive states. *)
Definition outcomes (g:CGS) (q:State) (c:coalition) (ss:strategy_set g c) (l: computation g q) : Prop
:=
  forall (i:nat),
    S i  < (length (proj1_sig l)) ->
    forall (m:move_vec (nth i (proj1_sig l) q))
           (p:Player)
           (H: c p = true),
    let x := computation_prefix g q l i in
    m p = proj1_sig (ss p H q x) ->
    g.(d) (nth i (proj1_sig l) q) m = (nth (S i) (proj1_sig l) q).



(* Inductive type of a sentence in ATL. *)
Inductive sentence : Set :=
| obs : Observable -> sentence
| lnot : sentence -> sentence
| land : sentence -> sentence -> sentence
| lor : sentence -> sentence -> sentence
| possible_next : coalition -> sentence -> sentence
| possible_once : coalition -> sentence -> sentence
| possible_always : coalition -> sentence -> sentence
| possible_until : coalition -> sentence -> sentence -> sentence.

(* Notation for ATl sentences. *)
Notation "p //\\ q" := (land p q) (at level 30).
Notation "p \\// q" := (lor p q) (at level 30).
Notation "!! p" := (lnot p)  (at level 30).
Notation "p --> q" := (lnot (land (lnot p) q)) (at level 30).
Notation "<< c >>o p" := (possible_next c p) (at level 50).
Notation "<< c >>^ p" := (possible_once c  p) (at level 50).
Notation "<< c >># p" := (possible_always c p) (at level 50).
Notation "<< c >> p %% q" := (possible_until c p q) (at level 50).
Notation "[[ c ]]o p" := (lnot (possible_next c (lnot p))) (at level 50).
Notation "[[ c ]]^ p" := (lnot (possible_always c (lnot p))) (at level 50).
Notation "[[ c ]]# p" := (lnot (possible_once c (lnot p)))  (at level 50).
Notation "[[ c ]] p %% q" := (lnot (possible_until c (lnot q) p)) (at level 50).

Check forall  (g:CGS) (q:State) (c: coalition),
    exists (ss:strategy_set g c),
      forall (l:computation g q),
        outcomes g q c ss l.

(* Variable not_helper : CGS -> State -> sentence -> Prop. *)

(* Inductive verifiesI: CGS -> State -> sentence -> Prop := *)
(* | verifiesObs: forall (g: CGS) (q: State) (a: Observable), *)
(*     g.(o) q = a -> verifiesI g q (obs a) *)
(* | verifiesNot: forall (g: CGS) (q: State) (phi: sentence), *)
(*     ~ not_helper g q phi -> *)
(*     verifiesI g q (!! phi) *)
(* | verifiesAnd: forall (g: CGS) (q: State) (phi1 phi2: sentence), *)
(*     verifiesI g q phi1 -> *)
(*     verifiesI g q phi2 -> *)
(*     verifiesI g q (phi1 //\\ phi2) *)
(* | verifiesPossibleNext: forall (g: CGS) (q: State) (phi: sentence) (c:coalition), *)
(*     (exists (ss:strategy_set g c), *)
(*       forall (l:computation g q), *)
(*         outcomes g q c ss l -> *)
(*         verifiesI g (nth 1 (proj1_sig l) q) phi) -> *)
(*     verifiesI g q (<<c>>o phi) *)
(* | verifiesPossibleOnce: forall (g: CGS) (q: State) (phi: sentence) (c:coalition), *)
(*     (exists (ss:strategy_set g c), *)
(*         forall (l:computation g q), *)
(*           outcomes g q c ss l -> *)
(*           (exists n:nat, verifiesI g (nth n (proj1_sig l) q) phi)) -> *)
(*     verifiesI g q (<<c>>^ phi) *)
(* | verifiesPossibleAlways: forall (g: CGS) (q: State) (phi: sentence) (c:coalition), *)
(*     (exists (ss:strategy_set g c), *)
(*         forall (l:computation g q), *)
(*           outcomes g q c ss l -> *)
(*           (forall n:nat, verifiesI g (nth n (proj1_sig l) q) phi)) -> *)
(*     verifiesI g q (<<c>>^ phi). *)
 

    
    
Fixpoint verifies (g:CGS) (q:State) (phi:sentence) :Prop :=
  match phi with
  | obs a => g.(o) q = a
  | !! a => ~ (verifies g q a)
  | a //\\ b => (verifies g q a) /\ (verifies g q b)
  | a \\// b => (verifies g q a) \/ (verifies g q b)
  | <<c>>o a => exists (ss:strategy_set g c),
                forall (l:computation g q),
                  outcomes g q c ss l ->
                  (verifies g (nth 1 (proj1_sig l) q) a)
  | <<c>>^ a => exists (ss:strategy_set g c),
                forall (l:computation g q),
                  outcomes g q c ss l ->
                  exists (n:nat),
                    (verifies g (nth n (proj1_sig l) q) a)
  | <<c>># a => exists (ss:strategy_set g c),
                forall (l:computation g q),
                  outcomes g q c ss l ->
                  forall (n:nat),
                    (verifies g (nth n (proj1_sig l) q) a)
  | <<c>> a %% b => exists (ss:strategy_set g c),
                    forall (l:computation g q),
                      outcomes g q c ss l ->
                      exists (n:nat),
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

Theorem once_not_always_not : forall (g:CGS) (q:State) (phi:sentence) (c:coalition),
    verifies g q  (<<c>>^ phi) <-> verifies g q (!! ([[c]]# (!! phi))).
Proof.
  intros. split.
  - assert (forall P:Prop, P -> ~~P).
    {
      intros. unfold not. intros. apply H0 in H. apply H.
    }
    simpl. intros. apply H.
    destruct H0. exists x. intros. apply H0 in H1. destruct H1. exists x0.
    apply H. apply H1.
  - simpl. intros. apply NNPP in H. destruct H. exists x. intros.
    apply H in H0. destruct H0. exists x0.
    apply NNPP in H0. apply H0.
    
Qed.


Theorem computation_property_q : forall (g:CGS) (q:State),
    computation_property g q (q::nil).
Proof.
  unfold computation_property. split.
  - reflexivity.
  - unfold computation_property_fix. simpl. apply I.
Qed.

Definition computation_q (g:CGS) (q:State) : computation g q := @exist (list State) (computation_property g q) (q::nil) (computation_property_q g q).

Theorem nth_computation_q : forall (g:CGS) (q:State) (n:nat),
    let l := computation_q g q in
    (nth n (proj1_sig l) q) = q.
Proof.
  intros. unfold computation_q in l. unfold l.
    unfold proj1_sig. assert (forall n, length (q::nil) <= (S n)).
    {
      simpl. induction n0.
      - reflexivity.
      - apply le_S. apply  IHn0.
    }
    induction n.
  - reflexivity.
  - pose proof (H n). pose proof (nth_overflow _ q H0). apply H1.
Qed.

Theorem zeroth_computation_is_q : forall (g:CGS) (q:State) (l: computation g q),
    (nth 0 (proj1_sig l) q) = q.
Proof.
  intros. destruct l. unfold computation_property in c. destruct c.
  simpl. induction x.
  - inversion e0.
  - inversion e0. reflexivity.
Qed.

Axiom computation_eq : forall (g:CGS) (q:State) (l1 l2:computation g q),
    l1 = l2 <-> (proj1_sig l1) = (proj1_sig l2).

Theorem ith_succ : (forall (g:CGS) (q:State) (l:list State) (i:nat), computation_property g q l -> S i < length l -> succ g (nth i l q) (nth (S i) l q)).
Proof.
  intros. generalize dependent i. generalize dependent q.
  induction l.
  - intros. inversion H0.
  - destruct l.
    + intros. inversion H0. inversion H2.
    + intros. inversion H. inversion H2.
      assert (hd_error (s::l) = Some s).
      {
        reflexivity.
      }
      assert (computation_property g s (s::l)).
      {
        unfold computation_property. split.
        - apply H5.
        - apply H4.
      }
      pose proof (IHl s H6).
      assert (forall (i:nat) (a b:State) (l:list State), nth i l b = nth (S i) (a::l) b).
      {
        intros. destruct l0.
        - reflexivity.
        - reflexivity.
      }
      rewrite (nth_indep _ _ s H0).
      pose proof (Le.le_Sn_le _ _ H0). rewrite (nth_indep _ _ s H9).
      induction i.
      * simpl. apply H3.
      * rewrite <- H8. rewrite <- H8. apply H7. simpl. simpl in H0.
        apply le_S_n. apply H0.
Qed.

Theorem coalition_complement_next : forall (g:CGS) (q:State) (phi:sentence) (c:coalition),
    verifies g q (<<c>>o phi) <-> verifies g q ([[coal_comp c]]o phi).
Proof.
Admitted.
  
Theorem coalition_complement_once_always : forall (g:CGS) (q:State) (phi:sentence) (c:coalition),
    verifies g q (<<c>>^ phi) <-> verifies g q ([[coal_comp c]]^ phi).
Proof.
Admitted.

Theorem coalition_complement_until : forall (g:CGS) (q:State) (phi psi:sentence) (c:coalition),
    verifies g q (<<c>> phi %% psi) <-> verifies g q ([[coal_comp c]] phi %% psi).
Proof.
Admitted.