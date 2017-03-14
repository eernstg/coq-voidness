Require Import Utf8.
Require Import List.
Require Import ClassTestTypes.
Require Import VoidnessPreservation.

(* Works with multiple parameters, with no changes: Uncomment one of them. *)
Module MyVoidness :=
  Voidness.NormalVoidness.
  (* Voidness.PermissiveVoidness. *)

Module MyVoidnessPreservation :=
  VoidnessPreservation.VoidnessPreservationBase MyVoidness.
Import MyVoidnessPreservation.

(* -------------------- Examples from email threads -------------------- *)

(* A<Object> x = new A<void>(); // No *)
Goal ~(TypeVoidnessPreserves dt_A_void dt_A_Object).
  unfold not. intro H. inversion H. inversion H2. inversion H5.
    inversion H8. apply H14. reflexivity.
  inversion H8.
    inversion H12. inversion H19.
  inversion H13. inversion H17.
Qed.

(* A<dynamic> x = new A<void>(); // Yes *)
Goal TypeVoidnessPreserves dt_A_void dt_A_dynamic.
  unfold TypeVoidnessPreserves. simpl. auto 7.
Qed.

(* A<Object> x = new A<dynamic>(); // Yes *)
Goal TypeVoidnessPreserves dt_A_dynamic dt_A_Object.
  unfold TypeVoidnessPreserves. simpl. auto 7.
Qed.

(* A<void> x = new A<dynamic>(); // voidV = dynamicV, yes *)
Goal TypeVoidnessPreserves dt_A_dynamic dt_A_void.
  unfold TypeVoidnessPreserves. simpl. auto 7.
Qed.

(* A<void> x = new A<Object>(); // voidV = objectV, Yes *)
Goal TypeVoidnessPreserves dt_A_Object dt_A_void.
  unfold TypeVoidnessPreserves. simpl. auto 7.
Qed.

(* dynamic x = new A<void>(); // Yes *)
Goal TypeVoidnessPreserves dt_A_void dt_dynamic.
  unfold TypeVoidnessPreserves. simpl. auto 7.
Qed.

(* Object x = new A<void>(); // Yes *)
Goal TypeVoidnessPreserves dt_A_void dt_Object.
  unfold TypeVoidnessPreserves. simpl.
  apply vp_class. apply vctsp_cons.
    apply vctp_gone. apply vctg_cons.
      discriminate.
    apply vctg_nil.
  apply vctsp_cons.
    apply vctp_some. auto.
  auto.
Qed.

(* Iterable<void> x = new List<void>(); // Yes *)
Goal TypeVoidnessPreserves dt_List_void dt_Iterable_void.
  unfold TypeVoidnessPreserves. simpl.
  apply vp_class. apply vctsp_cons.
    apply vctp_gone; apply vctg_cons.
      discriminate.
    apply vctg_cons.
      discriminate.
    auto.
  apply vctsp_cons.
    apply vctp_some. apply vctps_first. auto.
  apply vctsp_cons.
    apply vctp_some. apply vctps_rest. apply vctps_first. auto.
  auto.
Qed.

(* List<void> x = new Iterable<void>(); // Yes *)
Goal TypeVoidnessPreserves dt_Iterable_void dt_List_void.
  unfold TypeVoidnessPreserves. simpl. auto 8.
Qed.

(* Iterable<Object> x = new List<void>(); // No *)
Goal ~(TypeVoidnessPreserves dt_List_void dt_Iterable_Object).
  unfold TypeVoidnessPreserves.
  simpl. unfold not. intros. inversion H.
  inversion H2. inversion H7. inversion H10.
    inversion H13. apply H19. reflexivity.
  inversion H13.
    inversion H17. inversion H24.
  inversion H18. inversion H22.
Qed.

(* List<Object> x = new Iterable<void>(); // No *)
Goal ~(TypeVoidnessPreserves dt_Iterable_void dt_List_Object).
  unfold TypeVoidnessPreserves.
  simpl. unfold not. intros. inversion H.
  inversion H2. inversion H5.
    inversion H8. inversion H17. apply H21. reflexivity.
  inversion H8. inversion H13.
    inversion H16. inversion H23.
  inversion H17. inversion H21.
Qed.
