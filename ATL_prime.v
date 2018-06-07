(* Alternating-Time Temporal Logic - a version without negative Observables *)
Require Export CGS.

(* Inductive type of a sentence in (incomplete) propositional logic. *)
Inductive prop_sentence : Set :=
| obs : Observable -> prop_sentence
| pand : prop_sentence -> prop_sentence -> prop_sentence
| por :  prop_sentence -> prop_sentence -> prop_sentence.


(* Inductive type of a sentence in ATL. *)
Inductive sentence : Set :=
| prop : prop_sentence -> sentence
| possible_next : coalition -> sentence -> sentence
| possible_once : coalition -> sentence -> sentence
| possible_always : coalition -> sentence -> sentence
| possible_until : coalition -> sentence -> sentence -> sentence
| necessary_next : coalition -> sentence -> sentence
| necessary_once : coalition -> sentence -> sentence
| necessary_always : coalition -> sentence -> sentence
| necessary_until : coalition -> sentence -> sentence -> sentence.

(* Notation for ATl sentences. *)
Notation "p //\\ q" := (pand p q) (at level 30).
Notation "p \\// q" := (por p q) (at level 30).
Notation "<< c >>o p" := (possible_next c p) (at level 50).
Notation "<< c >>^ p" := (possible_once c  p) (at level 50).
Notation "<< c >># p" := (possible_always c p) (at level 50).
Notation "<< c >> p %% q" := (possible_until c p q) (at level 50).
Notation "[[ c ]]o p" := (necessary_next c p) (at level 50).
Notation "[[ c ]]^ p" := (necessary_once c p) (at level 50).
Notation "[[ c ]]# p" := (necessary_always c p)  (at level 50).
Notation "[[ c ]] p %% q" := (necessary_until c p q) (at level 50).

Inductive prop_verifies : CGS -> State -> prop_sentence -> Prop :=
| verifiesObs : forall (g:CGS) (q:State) (a:Observable),
    beq_observable (g.(o) q) a = true ->
    prop_verifies g q (obs a)
| verifiesAnd : forall (g:CGS) (q:State) (phi psi : prop_sentence),
    (prop_verifies g q phi /\ prop_verifies g q psi) ->
    prop_verifies g q (phi //\\ psi)
| verifiesOr : forall (g:CGS) (q:State) (phi psi : prop_sentence),
    (prop_verifies g q phi \/ prop_verifies g q psi) ->
    prop_verifies g q (phi \\// psi).

Inductive verifies: CGS -> State -> sentence -> Prop :=
| verifiesPossibleNext: forall (g: CGS) (q: State) (phi: sentence) (c:coalition),
    (exists (ss:strategy_set g c),
        forall (l:Stream State) (CPL: computation_property g q l),
          outcomes g c ss l ->
          verifies g (Str_nth 1 l) phi) ->
    verifies g q (<<c>>o phi)
| verifiesPossibleOnce: forall (g: CGS) (q: State) (phi: sentence) (c:coalition),
    (exists (ss:strategy_set g c),
        forall (l:Stream State) (CPL: computation_property g q l),
          outcomes g c ss l ->
          (exists n:nat, verifies g (Str_nth n l) phi)) ->
    verifies g q (<<c>>^ phi)
| verifiesPossibleAlways: forall (g: CGS) (q: State) (phi: sentence) (c:coalition),
    (exists (ss:strategy_set g c),
        forall (l:Stream State) (CPL: computation_property g q l),
                  outcomes g c ss l ->
          (forall n:nat, verifies g (Str_nth n l) phi)) ->
    verifies g q (<<c>># phi)
| verifiesPossibleUntil : forall (g: CGS) (q: State) (phi psi: sentence) (c:coalition),
    (exists (ss:strategy_set g c),
        forall (l:Stream State) (CPL: computation_property g q l),
          outcomes g c ss l ->
          (exists (n:nat),
              (verifies g (Str_nth n l) psi) /\
              (forall m:nat, verifies g (Str_nth m l) phi))) ->
    verifies g q (<<c>> phi %% psi)
| verifiesNecessaryNext: forall (g: CGS) (q: State) (phi: sentence) (c:coalition),
    (forall (ss:strategy_set g c),
        exists (l:Stream State) (CPL: computation_property g q l),
          outcomes g c ss l /\
          verifies g (Str_nth 1 l) phi) ->
    verifies g q ([[c]]o phi)
| verifiesNecessaryOnce: forall (g: CGS) (q: State) (phi: sentence) (c:coalition),
    (forall (ss:strategy_set g c),
        exists (l:Stream State) (CPL: computation_property g q l),
          outcomes g c ss l /\
          (exists n:nat, verifies g (Str_nth n l) phi)) ->
    verifies g q ([[c]]^ phi)
| verifiesNecessaryAlways: forall (g: CGS) (q: State) (phi: sentence) (c:coalition),
    (forall (ss:strategy_set g c),
        exists (l:Stream State) (CPL: computation_property g q l),
          outcomes g c ss l /\
          (forall n:nat, verifies g (Str_nth n l) phi)) ->
    verifies g q ([[c]]# phi)
| verifiesNecessaryUntil : forall (g: CGS) (q: State) (phi psi: sentence) (c:coalition),
    (forall (ss:strategy_set g c),
        exists (l:Stream State) (CPL: computation_property g q l),
          outcomes g c ss l /\
          (exists (n:nat),
              (verifies g (Str_nth n l) psi) /\
              (forall m:nat, verifies g (Str_nth m l) phi))) ->
    verifies g q (<<c>> phi %% psi).


    
    
Definition invariant (g1 g2:CGS) : Prop := forall (phi:sentence) (q:State),
    verifies g1 q phi <-> verifies g2 q phi.
    
(* TODO: invariance. *)
(* TODO: proof calculus *)

Definition spec : Type := State -> sentence -> Prop.

Definition g_in_spec (sp:spec) (g:CGS) (q:State) : Prop := forall (phi:sentence), sp q phi -> verifies g q phi.


Theorem coal_comp_comp : forall c, coal_comp (coal_comp c) = c.
Proof.
  intros.
  unfold coal_comp. intros. apply functional_extensionality. intros. destruct (c x).
  - reflexivity.
  - reflexivity.
Qed.
  
Axiom d_sentence : forall (g:CGS) (q:State) (phi:sentence), decidable (verifies g q phi).



Theorem coalition_complement_next : forall (g:CGS) (q:State) (phi:sentence) (c:coalition),
    verifies g q (<<c>>o phi) <-> verifies g q ([[coal_comp c]]o phi).
Proof.
Admitted.
  (* intros. split. *)
  (* - intros. inversion H. apply verifiesNecessaryNext. *)
  (*   pose proof (H3 (sq q) (computation_property_sq g q)). *)
  (*   destruct H5. *)
  (*   exists (sq q). exists (computation_property_sq g q). intros. *)
  (*   assert (outcomes g c x (sq q)). *)
  (*   { *)
  (*     cofix OUT'. destruct (sq q), s0. *)
  (*     inversion OUT'. *)
  (*     apply (outcomes_cons g c x s s0 _ m CPL ENABLED DELTA OUT ). *)
  (*   } *)
  (*   apply H5 in H6. *)
  (*   split. *)
  (*   + cofix H7. destruct (sq q), s0. *)
  (*     inversion H7. *)
  (*     apply (outcomes_cons g (coal_comp c) ss s s0 _ m CPL ENABLED DELTA OUT). *)
  (*   + apply H6. *)
  (* - intros. inversion H. apply verifiesPossibleNext. *)
  (*   intros. *)
  (*   destruct H3, H3. *)
    
Theorem coalition_complement_once_always : forall (g:CGS) (q:State) (phi:sentence) (c:coalition),
    verifies g q (<<c>>^ phi) <-> verifies g q ([[coal_comp c]]^ phi).
Proof.
Admitted.

Theorem coalition_complement_until : forall (g:CGS) (q:State) (phi psi:sentence) (c:coalition),
    verifies g q (<<c>> phi %% psi) <-> verifies g q ([[coal_comp c]] phi %% psi).
Proof.
Admitted.

(* Create HintDb verifies. *)
(* Hint Resolve coalitiion_complement_next : verifies. *)

(* auto with verifies *)