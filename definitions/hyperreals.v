(*Require Import Coq.ZArith.Z.

(* Step 1: Define the hyperreal numbers *)
Inductive Hyperreal :=
  | hyperreal : Z -> Q -> Hyperreal.
*)
  Theorem plus_comm : forall n m : nat,
  n + m = m + n.
Proof.
  intros n m.
  induction n as [| n' IHn'].
  - simpl. rewrite <- plus_n_O. reflexivity.
  - simpl. rewrite IHn'. rewrite <- plus_n_Sm. reflexivity.
Qed.

(* Step 2: Define the standard part function *)
Definition standard_part (x: Hyperreal) : option Q :=
  match x with
  | hyperreal n r => if (Qle_bool (-1 # 1) r && Qle_bool r (1 # 1)) then Some r else None
  end.
