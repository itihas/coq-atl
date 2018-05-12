Require Export ATL.
Require Export List.
Require Export Nat.
Require Extraction.
Extraction Language Haskell.

Parameter assignment : Observable -> Player -> nat.

Definition reachable_payoffs_property (g:CGS)
         (q:State)
         (c:coalition)
         (o:Observable)
  : Prop :=
  forall (p:Player),
    c p ->
    verifies g q (<< c >>^ (obs o)).

Check reachable_payoffs_property.

Definition spec_reachable_payoffs_property (sp:spec)
           (q:State)
           (c:coalition)
           (o:Observable)
  :=
    forall(g:CGS), g_in_spec sp g q ->
                             reachable_payoffs_property g q c o.

Definition spec_reachable_payoffs (sp:spec) (q:State) (c:coalition) : Type
  := {o:Observable | spec_reachable_payoffs_property sp q c o}.

Definition core (g:CGS) (q:State) (o: Observable)  : Prop :=
  reachable_payoffs_property g q grand o
  /\ (forall (o':Observable),
         reachable_payoffs_property g q grand o' ->
         (forall (p:Player),
             assignment o' p <= assignment o p))
    /\ (forall c:coalition,
           (forall (o':Observable),
               reachable_payoffs_property g q c o' ->
               (forall (p:Player),
                   c p ->
                   assignment o' p <= assignment o p))).

Definition listp_to_coalition (lp:list Player) : coalition := fun p => In p lp.

Axiom core_must_happen : forall (g:CGS) (q:State) (o:Observable),
    core g q o -> reachable_payoffs_property g q nobody o.

Theorem sp_core_must_happen : forall (sp:spec) (o:Observable) (c:coalition) (g:CGS) (q:State),
    g_in_spec sp g q -> core g q o -> reachable_payoffs_property g q nobody o.
Proof.
  intros. apply core_must_happen. apply H0.
Qed.

