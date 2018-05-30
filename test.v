Require Import ATL.


Variable q:State.
Variable m:Move.

Definition test_move_vec : move_vec q := fun p:Player => m.


Definition test_move_function : move_function := fun (q:State) (p:Player) => m.

  