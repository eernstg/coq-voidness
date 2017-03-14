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

(* ---------- Voidness Types ---------- *)

(* Object *)
Definition cvt_Object : VoidnessClassTypes := (Object, nil) :: nil.
Definition vt_Object := vt_class cvt_Object.

(* A<Object> *)
Definition cvt_A_Object := (A, vt_Object :: nil) :: cvt_Object.
Definition vt_A_Object := vt_class cvt_A_Object.

(* A<1> *)
Definition cvt_A_1 := (A, vt_1 :: nil) :: cvt_Object.
Definition vt_A_1 := vt_class cvt_A_1.

(* A<A<1>> *)
Definition cvt_A_A_1 := (A, vt_A_1 :: nil) :: cvt_Object.
Definition vt_A_A_1 := vt_class cvt_A_A_1.

(* B<A<1>, Object> *)
Definition cvt_B_A1_Object := (B, vt_A_1 :: vt_Object :: nil) :: cvt_Object.
Definition vt_B_A1_Object := vt_class cvt_B_A1_Object.

(* B<Object, Object> *)
Definition cvt_B_ObjectObject := (B, vt_Object :: vt_Object :: nil) :: cvt_Object.
Definition vt_B_ObjectObject := vt_class cvt_B_ObjectObject.

Hint Unfold
  ct_Object dt_Object ct_A_Object dt_A_Object ct_A_void dt_A_void
  ct_A_dynamic dt_A_dynamic ct_Iterable_Object dt_Iterable_Object
  ct_Iterable_void dt_Iterable_void ct_List_Object dt_List_Object
  ct_List_void dt_List_void cvt_Object vt_Object cvt_A_Object
  vt_A_Object cvt_A_1 vt_A_1 cvt_A_A_1 vt_A_A_1 cvt_B_A1_Object
  vt_B_A1_Object cvt_B_ObjectObject vt_B_ObjectObject.

(* ---------- Trying out existing examples ---------- *)

(* 0 <:: 0 *)
Goal VoidnessPreserves vt_0 vt_0.
 auto.
Qed.

(* 0 <:: 1 *)
Goal VoidnessPreserves vt_0 vt_1.
  auto.
Qed.

(* A<Object> <:: A<1> *)
Goal VoidnessPreserves vt_A_Object vt_A_1.
  apply vp_class; apply vctsp_cons.
    apply vctp_some; apply vctps_first; auto.
  apply vctsp_cons; auto.
  apply vctp_some. apply vctps_rest. apply vctps_first. auto.
Qed.

(* A<A<1>> <:: A<1> *)
Goal VoidnessPreserves vt_A_A_1 vt_A_1.
  apply vp_class; apply vctsp_cons; auto.
    apply vctp_some. apply vctps_first. apply vpp_cons; auto.
  apply vctsp_cons; auto. apply vctp_some. apply vctps_rest. apply vctps_first. auto.
Qed.

Goal ~(VoidnessPreserves vt_A_1 vt_A_Object).
  unfold not. intro H. inversion H. inversion H2. inversion H5.
    inversion H8. apply H14. reflexivity.
  inversion H8.
    inversion H12. inversion H19.
  inversion H13. inversion H17.
Qed.
