Require Import ATL.


Variable q:State.
Variable m:Move.

Definition test_move_vec : move_vec q := fun p:Player => m.

Check test_move_vec.  
                         