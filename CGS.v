Require Export List.
Require Export Classical.
Require Export Decidable.
Require Export FunctionalExtensionality.
Require Export Streams.

Require Import Coq.Lists.List Coq.Bool.Bool.

Import Coq.Lists.List.ListNotations.

Scheme Equality for list.

Parameter State : Set.
Parameter Player : Set.
Parameter Observable : Set.     (* set of atomic truths that can hold at a given state. *)
Parameter Move : Set.           (* alphabet of moves individual players can make.*)



Parameter beq_state : State -> State -> bool.
Parameter beq_player : Player -> Player -> bool.
Parameter beq_observable : Observable -> Observable -> bool.

Axiom beq_state_refl : forall (q:State), beq_state q q = true.
Axiom beq_player_refl : forall (p:Player), beq_player p p = true.
Axiom beq_observable_refl : forall (o:Observable), beq_observable o o = true.

Axiom beq_state_Prop : forall (q1 q2:State), beq_state q1 q2 = true -> q1 = q2.
Axiom beq_player_Prop : forall (p1 p2:Player), beq_player p1 p2 = true -> p1 = p2.
Axiom beq_obervable_Prop : forall (o1 o2:Observable), beq_observable o1 o2 = true -> o1 = o2.

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

Fixpoint Stream_firstn {A:Type} (i:nat) (s:Stream A) : list A :=
  match i with
  | 0 => nil
  | S i => match s with
           | Cons a b => a :: Stream_firstn i b
           end
  end.
  

(* [computation_property_fix] checks that successive states are successors according to the above property. *)

Inductive computation_property_finite: CGS -> State -> list State -> Prop :=
| computation_property_finite_one : forall (g:CGS) (s : State),
    computation_property_finite g s (s::nil)
| computation_property_finite_cons: forall (g: CGS) (ss: list State) (s1 s2: State)
    (FIXSUCC: computation_property_finite g s2 (s2::ss))
    (SUCC: succ g s1 s2),
    computation_property_finite g s1 (s1::s2::ss).

CoInductive computation_property: CGS -> State -> Stream State -> Prop :=
| computation_property_cons: forall (g: CGS) (ss: Stream State) (s1 s2: State)
    (FIXSUCC: computation_property g s2 (Cons s2 ss))
    (SUCC: succ g s1 s2),
    computation_property g s1 (Cons s1 (Cons s2 ss)).


Theorem computation_property_prefix : forall (g:CGS) (q:State) (l:Stream State) (i:nat),
    computation_property g q l -> computation_property_finite g q (Stream_firstn (S i) l).
Proof.
  Admitted.


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

CoFixpoint sq (q:State) : Stream State :=
  Cons q (sq q).

Theorem computation_property_sq : forall g q, computation_property g q (sq q).
Proof.
Admitted.
  
(* A strategy is a function from computations to moves, representing what a player would do in a particular play-through. *)

(* Inductive strategy (g:CGS) (p:Player) : (nonempty State) -> Move -> Set := *)
(*   strat : forall (l:nonempty State) (m:Move) *)
(*                  (ENABLED: g.(e) (nonempty_last l) p m = true), *)
(*     strategy g p l m. *)

(* Definition strat_nothing (g:CGS) (p:Player) := *)
(*   fun l => strat g p l nothing (nothing_always_enabled g (nonempty_last l) p). *)


Definition strategy (g:CGS) (p:Player) : Set := forall (l:list State) (q:State) (CPL: computation_property_finite g q l), Move.

Definition strategy_legal (g:CGS) (p:Player) (s:strategy g p) :=
  forall (l:list State) (q:State) (CPL: computation_property_finite g q l),
    g.(e) (last l q) p (s l q CPL) = true.

Definition strat_nothing (g: CGS) (p:Player) : strategy g p :=
  fun l _ _ => nothing.

Check strat_nothing.

Theorem nothing_always_legal : forall (g:CGS) (p:Player),
    strategy_legal g p (strat_nothing g p).
Proof.
  unfold strategy_legal. intros. apply nothing_always_enabled.
Qed.

(* [strategy_set] is a type representing unique strategies only of members in the coalition. *)
Definition strategy_set (g:CGS) (c:coalition) :=
  forall (p:Player)
         (COAL: c p = true),
    {s: strategy g p | strategy_legal g p s}.


(* Strategy set where members of the coalition do nothing. *)
Definition ss_nothing (g:CGS) (c:coalition) : strategy_set g c := fun p COAL => exist (strategy_legal g p) (strat_nothing g p) (nothing_always_legal g p).

Check ss_nothing.


(* Whether a particular move vector obeys a given strategy set. *)
Definition strategy_set_enabled
           (g:CGS)
           (c:coalition)
           (ss:strategy_set g c)
           (l:list State)
           (q:State)
           (CPL: computation_property_finite g q l)
           (m:move_vec) :=
  forall (p:Player) (COAL: c p = true),
  match (ss p COAL) with
  | exist _ s _ =>  m (last l q) p  = s l q CPL
  end.
(* TODO make [strategy_set], [strategy] inductive *)


CoInductive outcomes (g:CGS) (c: coalition) : (strategy_set g c) -> Stream State -> Prop :=
| outcomes_cons : forall (ss:strategy_set g c) (q1 q2:State)
                         (l:Stream State)
                         (m:move_vec)
                         (CPL: computation_property g q1 (Cons q1 (Cons q2 l)))
                         (ENABLED : strategy_set_enabled g c ss (q1::nil) q1 (computation_property_prefix g q1 (Cons q1 (Cons q2 l)) 0 CPL) m)
                         (DELTA: g.(d) q1 m = q2)
                         (OUT: outcomes g c ss (Cons q2 l)),
      outcomes g c ss (Cons q1 (Cons q2 l)).
           
