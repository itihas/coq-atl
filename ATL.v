(* Alternating-Time Temporal Logic *)
Require Export CGS.
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
Notation "p --> q" := (lor (lnot p) q) (at level 30).
Notation "<< c >>o p" := (possible_next c p) (at level 50).
Notation "<< c >>^ p" := (possible_once c  p) (at level 50).
Notation "<< c >># p" := (possible_always c p) (at level 50).
Notation "<< c >> p %% q" := (possible_until c p q) (at level 50).
Notation "[[ c ]]o p" := (lnot (possible_next c (lnot p))) (at level 50).
Notation "[[ c ]]^ p" := (lnot (possible_always c (lnot p))) (at level 50).
Notation "[[ c ]]# p" := (lnot (possible_once c (lnot p)))  (at level 50).
Notation "[[ c ]] p %% q" := (lnot (possible_until c (lnot q) p)) (at level 50).

    
    
Fixpoint verifies (g:CGS) (q:State) (phi:sentence) : Prop :=
  match phi with
  | obs a => beq_observable (g.(o) q) a = true
  | !! a => ~ (verifies g q a)
  | a //\\ b => (verifies g q a) /\ (verifies g q b)
  | a \\// b => (verifies g q a) \/ (verifies g q b)
  | <<c>>o a => exists (ss:strategy_set g c),
                forall (l:Stream State) (CPL: computation_property g q l),
                  outcomes g c ss l ->
                  (verifies g (Str_nth 1 l) a)
  | <<c>>^ a => exists (ss:strategy_set g c),
                forall (l:Stream State) (CPL:computation_property g q l),
                  outcomes g c ss l ->
                  exists (n:nat),
                    (verifies g (Str_nth n l) a)
  | <<c>># a => exists (ss:strategy_set g c),
                forall (l:Stream State) (CPL:computation_property g q l),
                  outcomes g c ss l ->
                  forall (n:nat),
                    (verifies g (Str_nth n l) a)
  | <<c>> a %% b => exists (ss:strategy_set g c),
                forall (l:Stream State) (CPL:computation_property g q l),
                      outcomes g c ss l ->
                      exists (n:nat),
                        ((verifies g (Str_nth n l) b)
                         /\ forall (m:nat),
                            m < n -> (verifies g (Str_nth m l) a))
  end.
(* TODO write tactic to step through the fixpoint.

The way that I know how to do this is to write lemmas that show
what happens on one step. Eg:
Lemma verifies_step_and: verifies(g q (a//\\b)) = 
     verifies g q a /\ verifies g q b.
Proof.
unfold _.
simpl _.
reflexivity.
Qed.

Ltac stepverifies := first [rewrite verifies_step_and, rewrite verifies_step_or, rewrite verifies_step_*];
Ltac simplpverifies := repeat stepverifies.
 *)
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
    apply H. apply H1. apply CPL.
  - simpl. intros. apply NNPP in H. destruct H. exists x. intros.
    apply H in H0. destruct H0. exists x0.
    apply NNPP in H0. apply H0. apply CPL.
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

(* Create HintDb verifies. *)
(* Hint Resolve coalitiion_complement_next : verifies. *)

(* auto with verifies *)