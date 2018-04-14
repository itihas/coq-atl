Require Export ATL.
Require Export List.
Require Export Nat.
Require Extraction.
Extraction Language Haskell.

Parameter assignment : Observable -> Player -> nat.
Parameter o0 : Observable.
Definition reachable_payoffs_property (g:CGS)
         (q:State)
         (c:coalition)
         (o:Observable)
  : Prop :=
  forall (p:Player),
    c p ->
    @verifies g q (<< c >>^ (obs o)).

Check reachable_payoffs_property.

Definition reachable_payoffs (g:CGS) (q:State) (c:coalition) : Set
           := {o:Observable | reachable_payoffs_property g q c o}.

Definition spec_reachable_payoffs_property (sp:spec)
           (q:State)
           (c:coalition)
           (o:Observable)
  :=
    forall (phi:sentence) (g:CGS), sp phi ->
                                   @verifies g q phi ->
                                   reachable_payoffs_property g q c o.

Definition spec_reachable_payoffs (sp:spec) (q:State) (c:coalition) : Type
  := {o:Observable | spec_reachable_payoffs_property sp q c o}.

Definition core (g:CGS) (q:State) (c:coalition) (o: Observable)  : Prop :=
  @verifies g q ( <<c>>^ obs o )
  /\ forall (p:Player) (r:reachable_payoffs g q c) (c':coalition),
    let o' := proj1_sig r in
    c p -> c' p -> assignment o' p < assignment o p.

Definition listp_to_coalition (lp:list Player) : coalition := fun p => In p lp.

Definition core' (g:CGS) (q:State) (lo:list Observable): list  (Observable * (list coalition))
  :=let c_helper
        := fix ch (current: list Player) (o:Observable)
             := match current with
                | nil => true
                | p::current' => 
                  if
                    fold_left (fun b o' =>
                                 andb b (leb (assignment o' p)
                                             (assignment o p)))
                              lo true
                  then ch current' o
                  else false
                end
    in
    let helper
        := fix fh (remaining current :list Player) (result:list (list Player)) (o:Observable)
             := match remaining with
                | nil => if c_helper current o then current::result else result
                | p::remaining' =>
                   let r := fh remaining' (p::current) result o
                   in fh remaining' current r o
                end
    in (map (fun o => (o, (map listp_to_coalition (helper g.(lp) nil nil o))))
                      lo).
