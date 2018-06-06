Require Export List.
Require Export Classical.
Require Export Decidable.
Require Export FunctionalExtensionality.


Require Export NonEmpty.
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
Parameter beq_observable : Observable -> Observable -> bool.
(* type corresponding to the set of moves each player makes. *)
Definition move_vec := State -> Player -> Move.

(* AHK says not all moves are available at all states. We express this using a function type [enabled], expressing which moves are available at which state.  *)
Definition enabled := State -> Player -> Move -> bool.

(* labeling function type. *)
Definition observation := State -> Observable.

(* transition function. *)
Definition delta := State -> move_vec -> State.

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
  exists mv:move_vec,
    (forall (p:Player),
        (g.(e) q p (mv q p)) = true) /\
    q'=g.(d) q mv.

(* Computations are nonempty sequences of states [l] where every [l_(i+1)] is a successor of [l_i]. *)


(* [computation_property_fix] checks that successive states are successors according to the above property. *)

Inductive computation_property: CGS -> State -> nonempty State -> Prop :=
| computation_property_one: forall (g: CGS) (s: State),
    computation_property g s (s:::nil)
| computation_property_cons: forall (g: CGS) (ss: list State) (s1 s2: State)
    (FIXSUCC: computation_property g s2 (s2 :::ss ))
    (SUCC: succ g s1 s2),
    computation_property g s1 (s1:::s2::ss).



(* Subset type of [list State] where [computation_property] holds. *)
(* )Definition computation (g:CGS) (q:State) : Set := {l:list State | computation_property g q l}.
 *)


(* If a [list State] is a [q]-computation, that same [list State] cons'ed with State [a] is an [a]-computation. *)
(* Theorem computation_property_cons : *)
(*   forall (g:CGS) (l:list State) (q a b:State), *)
(*     computation_property g q (b::l) /\ succ g a b -> computation_property g a (a::b::l). *)
(* Proof. *)
(*   intros. destruct H. destruct H. unfold computation_property. split. *)
(*   - reflexivity. *)
(*   - simpl. split. *)
(*     + apply H0. *)
(*     + simpl in H1. apply H1. *)
(* Qed. *)

(* (* A list has length > 0 iff there exists a head to the list.*) *)
(* Theorem  length_hd_error : forall (A:Type) (l:list A), 1 <= length l <-> exists y:A, hd_error l = Some y. *)
(* Proof. *)
(* intros. split. *)
(* - induction l. *)
(*   + intros. inversion H. *)
(*   + intros. exists a. reflexivity. *)
(* - intros. destruct H. assert (x::(tl l) = l). *)
(*   { symmetry. apply hd_error_tl_repr. split. *)
(*     - apply H. *)
(*     - reflexivity. *)
(*   } *)
(*   rewrite <- H0. simpl. induction (length (tl l)). *)
(*   + reflexivity. *)
(*   + apply le_S. apply IHn. *)
(* Qed. *)

(* (* The head of a list [b0++b1] is the head of list [b0] if [b0] is nonempty.*) *)
(* Theorem hd_error_app : forall (b0 b1: list State) (a:State), hd_error b0 = Some a -> (hd_error (b0 ++ b1)) = Some a. *)
(*   { *)
(*     intros. induction b0. *)
(*     - inversion H. *)
(*     - simpl. simpl in H. apply H. *)
(*   } *)
(* Qed. *)

(* (* If [computation_property] holds for [l0++l1] and [l0] is nonempty, [computation_property] holds for [l0]. *) *)
(* Theorem computation_property_app : *)
(*   forall (g:CGS) (q:State) (l0 l1: list State), *)
(*     (1 <= (length l0)) -> computation_property g q (l0 ++ l1) -> computation_property g q l0. *)
(* Proof. *)
(*   intros. destruct H0. unfold computation_property. generalize dependent q. induction l0. *)
(*   - intros. inversion H. *)
(*   - intros. split. *)
(*     + simpl in H0. simpl. apply H0. *)
(*     + simpl. simpl in H1. simpl in H0. inversion H. *)
(*       * *)
(*         assert (hd_error l0 = None). *)
(*         { *)
(*           symmetry in H3. apply length_zero_iff_nil in H3. *)
(*           rewrite H3. reflexivity. *)
(*         } *)
(*         rewrite H2. apply I. *)
(*       *  *)
(*         assert (length l0 > 0). *)
(*         { unfold gt. unfold lt. apply H3. } *)
(*         apply length_hd_error in H3. destruct H3. apply (hd_error_app l0 l1 x) in H3. *)
(*         rewrite H3 in H1. destruct H1. apply (IHl0 H4 H5 x) in H3. *)
(*         destruct H3. *)
(*         rewrite H3. split. *)
(*         -- apply H1. *)
(*         -- apply H6. *)
(* Qed. *)

(* (* The nonempty prefix of a [q]-computation is a [q]-computation. *) *)
(* Theorem computation_property_prefix : *)
(*   forall (g:CGS) (n:nat) (q:State) (l:computation g q), *)
(*     computation_property g q (firstn (S n) (proj1_sig l)). *)
(* Proof. *)
(*   intros. destruct l. unfold proj1_sig. destruct c. *)
(*   pose proof (hd_error_app (firstn (S n) x) (skipn (S n) x) q) as H1. *)
(*   assert ((hd_error (firstn (S n) x)) = Some q). *)
(*   { *)
(*     simpl. destruct x. *)
(*     - apply H. *)
(*     - simpl. simpl in H. apply H. *)
(*   } *)
(*   apply H1 in H2. *)
(*   destruct (length_hd_error State x). *)
(*   assert (exists y, hd_error x = Some y). *)
(*   { exists q. apply H. } *)
(*   apply H4 in H5. *)
(*   pose proof (@computation_property_app g q (firstn (S n) x) (skipn (S n) x)). *)
(*   assert (1 <= length (firstn (S n) x)). *)
(*   { *)
(*     induction x. *)
(*     - inversion H. *)
(*     - simpl. induction (firstn n x). *)
(*       + reflexivity. *)
(*       + simpl. apply le_S. apply IHl. *)
(*   } *)
(*   assert (@computation_property g q x). *)
(*   { *)
(*     unfold computation_property. split. *)
(*     - apply H. *)
(*     - apply H0. *)
(*   } *)
(*   rewrite firstn_skipn in H6. *)
(*   apply (H6 H7 H8). *)
(* Qed. *)

(* (* A function generating the [n+1]-long prefix of a [q]-computation.*) *)
(* Definition computation_prefix *)
(*            (g:CGS) *)
(*            (q:State) *)
(*            (l: computation g q) *)
(*            (n:nat) *)
(*            : computation g q *)
(* := *)
(*   @exist (list State) *)
(*          (computation_property g q)(* (fun l => computation_property g q l) *) *)
(*          (firstn (S n) (proj1_sig l)) *)
(*          (computation_property_prefix g n q l). *)

(* Check computation_prefix. *)


(* There is always a move available called [nothing], which if performed by every player fails to change state. *)

(* A coalition is a set of players. *)
Definition coalition : Set := Player -> bool.

(* Coalition complement. *)
Definition coal_comp (c:coalition) : coalition := fun p:Player => negb (c p).

Definition grand (g:CGS) : coalition := fun _ => true.
Definition nobody : coalition := fun _ => false.

Definition coal_union (c1 c2 : coalition) : coalition := fun p => orb (c1 p) (c2 p).

Definition coal_intersection (c1 c2: coalition) : coalition := fun p => andb (c1 p) (c2 p).


Parameter nothing: Move.
Axiom nothing_always_enabled : forall (g:CGS) (q:State) (p:Player), g.(e) q p nothing = true.
Axiom nothing_does_nothing : forall (g:CGS) (q:State), g.(d) q (fun _ _ => nothing) = q.


(* A strategy is a function from computations to moves, representing what a player would do in a particular play-through. *)

(* Inductive strategy (g:CGS) (p:Player) : (nonempty State) -> Move -> Set := *)
(*   strat : forall (l:nonempty State) (m:Move) *)
(*                  (ENABLED: g.(e) (nonempty_last l) p m = true), *)
(*     strategy g p l m. *)

(* Definition strat_nothing (g:CGS) (p:Player) := *)
(*   fun l => strat g p l nothing (nothing_always_enabled g (nonempty_last l) p). *)


Definition strategy (g:CGS) (p:Player) : Set := forall (l:nonempty State) (q:State) (CPL: computation_property g q l), Move.

Definition strategy_legal (g:CGS) (p:Player) (s:strategy g p) :=
  forall (l:nonempty State) (q:State) (CPL: computation_property g q l),
    g.(e) (nonempty_last l) p (s l q CPL) = true.

Definition strat_nothing (g: CGS) (p:Player) : strategy g p :=
  fun l _ _ => nothing.

Check strat_nothing.

Theorem nothing_always_legal : forall (g:CGS) (p:Player),
    strategy_legal g p (strat_nothing g p).
Proof.
  unfold strategy_legal. intros. apply nothing_always_enabled.
Qed.

(* [strategy_set] is a type representing unique strategies only of members in the coalition. *)
Inductive strategy_set (g:CGS) (c:coalition) : Set :=
| strat_set : forall (p:Player)
                     (COAL: c p = true)
                     (s: strategy g p)
                     (SL: strategy_legal g p s),
    strategy_set g c.


(* Strategy set where members of the coalition do nothing. *)
Definition ss_nothing (g:CGS) (c:coalition) := fun p COAL => strat_set g c p COAL (strat_nothing g p) (nothing_always_legal g p).

Check ss_nothing.

(* Whether a particular move vector obeys a given strategy set. *)
Definition strategy_set_enabled
           (g:CGS)
           (c:coalition)
           (ss:strategy_set g c)
           (l:nonempty State)
           (q:State)
           (CPL: computation_property g q l)
           (mv:move_vec) :=
  match ss with
  | strat_set _ _ p _ s _ =>  mv (nonempty_last l) p  = s l q CPL
  end.
(* TODO make [strategy_set], [strategy] inductive *)


Inductive outcomes (g:CGS) (c: coalition) : (strategy_set g c) -> nonempty State -> Prop :=
| outcomes_two : forall (ss:strategy_set g c) (q1 q2:State)
                        (m: move_vec)
                        (CPL: computation_property g q1 (q1:::q2::nil))
                        (ENABLED: strategy_set_enabled g c ss (q1:::q2::nil) q1 CPL m)
                        (DELTA: g.(d) q1 m = q2),
    outcomes g c ss (q1:::q2::nil)
| outcomes_cons : forall (ss:strategy_set g c) (q:State)
                         (l:nonempty State)
                         (m:move_vec)
                         (CPL: computation_property g q (nonempty_cons q l))
                         (ENABLED : strategy_set_enabled g c ss (nonempty_cons q l) q CPL m)
                         (OUT: outcomes g c ss l),
      outcomes g c ss (nonempty_cons q l).
           
                        (* TODO finish redefining outcomes *)

(* Property checking whether a given computation obeys a strategy set in all successive states. *)
(* Definition outcomes (g:CGS) (q:State) (c:coalition) (ss:strategy_set g q c) (l: list State) (CPL: computation_property g q l) : Prop *)
(* := *)
(*   forall (i:nat), *)
(*     S i  < (length l) -> *)
(*     forall (m:move_vec) *)
(*            (p:Player) *)
(*            (H: c p = true), *)
(*     let x := firstn i l in *)
(*     m (nth i l q) p = ss p H x CPL -> *)
(*     g.(d) (nth i l q) m = (nth (S i) l q). *)


