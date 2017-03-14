Require Import Utf8.
Require Import List.
Require Import VoidnessPreservation.
Require Import InvariantVoidnessPreservation.
Require Import FunctionTestTypes.

(* This works, unchanged, with the regular and the invariant rules: Uncomment one *)
Module MyVoidnessPreservation :=
  VoidnessPreservation.VoidnessPreservationBase
  (* InvariantVoidnessPreservation.VoidnessPreservationBase *)
    Voidness.StrictVoidness.
Import MyVoidnessPreservation.

(* void Function(void) f = func<dynamic, dynamic>; // No *)
Goal ~(TypeVoidnessPreserves dt_fun_dynamic_dynamic dt_fun_void_void).
  intro H. inversion H. inversion H5. inversion H9.
Qed.

(* void Function(void) f = func<dynamic, void>; // No *)
Goal ~(TypeVoidnessPreserves dt_fun_dynamic_void dt_fun_void_void).
  intro H. inversion H. inversion H5. inversion H9.
Qed.

(* void Function(void) f = func<void, dynamic>; // Yes *)
Goal TypeVoidnessPreserves dt_fun_void_dynamic dt_fun_void_void.
  unfold TypeVoidnessPreserves.
  simpl. auto.
Qed.

(* void Function(void) f = func<Object, Object>; // No *)
Goal ~(TypeVoidnessPreserves dt_fun_Object_Object dt_fun_void_void).
  intro H. inversion H. inversion H5. inversion H9.
Qed.

(* void Function(void) f = func<Object, void>; // No *)
Goal ~(TypeVoidnessPreserves dt_fun_Object_void dt_fun_void_void).
  intro H. inversion H. inversion H5. inversion H9.
Qed.

(* void Function(void) f = func<void, Object>; // Yes *)
Goal TypeVoidnessPreserves dt_fun_void_Object dt_fun_void_void.
  unfold TypeVoidnessPreserves.
  simpl. auto.
Qed.

(* dynamic Function(dynamic) g = func<void, void>; // No *)
Goal ~(TypeVoidnessPreserves dt_fun_void_void dt_fun_dynamic_dynamic).
  intro H. inversion H. inversion H3.
Qed.

(* dynamic Function(dynamic) g = func<dynamic, void>; // No *)
Goal ~(TypeVoidnessPreserves dt_fun_dynamic_void dt_fun_dynamic_dynamic).
  intro H. inversion H. inversion H3.
Qed.

(* dynamic Function(dynamic) g = func<void, dynamic>; // Yes *)
Goal TypeVoidnessPreserves dt_fun_void_dynamic dt_fun_dynamic_dynamic.
  unfold TypeVoidnessPreserves.
  simpl. auto.
Qed.

(* dynamic Function(dynamic) g = func<Object, Object>; // Yes *)
Goal TypeVoidnessPreserves dt_fun_Object_Object dt_fun_dynamic_dynamic.
  unfold TypeVoidnessPreserves.
  simpl. auto.
Qed.

(* dynamic Function(dynamic) g = func<Object, void>; // No *)
Goal ~(TypeVoidnessPreserves dt_fun_Object_void dt_fun_dynamic_dynamic).
  intro H. inversion H. inversion H3.
Qed.

(* dynamic Function(dynamic) g = func<void, Object>; // Yes *)
Goal TypeVoidnessPreserves dt_fun_void_Object dt_fun_dynamic_dynamic.
  unfold TypeVoidnessPreserves.
  simpl. auto.
Qed.

(* Object Function(Object) h = func<void, void>; // No *)
Goal ~(TypeVoidnessPreserves dt_fun_void_void dt_fun_Object_Object).
  unfold TypeVoidnessPreserves.
  simpl. unfold not. intros. inversion H. inversion H3.
Qed.

(* Object Function(Object) h = func<dynamic, void>; // No *)
Goal ~(TypeVoidnessPreserves dt_fun_dynamic_void dt_fun_Object_Object).
  unfold TypeVoidnessPreserves.
  simpl. unfold not. intros. inversion H.
  inversion H3.
Qed.

(* Object Function(Object) h = func<void, dynamic>; // Yes *)
Goal TypeVoidnessPreserves dt_fun_void_dynamic dt_fun_Object_Object.
  unfold TypeVoidnessPreserves.
  simpl. auto.
Qed.

(* Object Function(Object) h = func<Object, Object>; // Yes *)
Goal TypeVoidnessPreserves dt_fun_Object_Object dt_fun_Object_Object.
  unfold TypeVoidnessPreserves.
  simpl. auto 7.
Qed.

(* Object Function(Object) h = func<Object, void>; // No *)
Goal ~(TypeVoidnessPreserves dt_fun_Object_void dt_fun_Object_Object).
  unfold TypeVoidnessPreserves.
  simpl. unfold not. intros. inversion H.
  inversion H3.
Qed.

(* Object Function(Object) h = func<void, Object>; // Yes *)
Goal TypeVoidnessPreserves dt_fun_void_Object dt_fun_Object_Object.
  unfold TypeVoidnessPreserves.
  simpl. auto 7.
Qed.

(* Object Function(void) h = func<Object, Object>; // No *)
Goal ~(TypeVoidnessPreserves dt_fun_Object_Object dt_fun_void_Object).
  intro H. inversion H. inversion H5. inversion H9.
Qed.

(* dynamic Function(void Function(void)) f = func<dynamic Function(dynamic), dynamic>; // No *)
Goal ~(TypeVoidnessPreserves dt_fun2_dynamic_dynamic dt_fun2_void_void).
  intro H. inversion H. inversion H5. inversion H9. inversion H15.
Qed.

(* dynamic Function(void Function(void)) f = func<Object Function(dynamic), dynamic>; // No *)
Goal ~(TypeVoidnessPreserves dt_fun2_dynamic_Object dt_fun2_void_void).
  intro H. inversion H. inversion H5. inversion H9. inversion H15.
Qed.

(* dynamic Function(void Function(void)) f = func<dynamic Function(Object), dynamic>; // No *)
Goal ~(TypeVoidnessPreserves dt_fun2_Object_dynamic dt_fun2_void_void).
  intro H. inversion H. inversion H5. inversion H9. inversion H15.
Qed.

(* dynamic Function(void Function(void)) f = func<Object Function(Object), dynamic>; // No *)
Goal ~(TypeVoidnessPreserves dt_fun2_Object_Object dt_fun2_void_void).
  intro H. inversion H. inversion H5. inversion H9. inversion H15.
Qed.

(* dynamic Function(dynamic Function(dynamic)) f = func<void Function(void), dynamic>; // No *)
Goal ~(TypeVoidnessPreserves dt_fun2_void_void dt_fun2_dynamic_dynamic).
  intro H. inversion H. inversion H5. inversion H9. inversion H17. inversion H21.
Qed.

(* dynamic Function(dynamic Function(dynamic)) f = func<Object Function(void), dynamic>; // No *)
Goal ~(TypeVoidnessPreserves dt_fun2_void_Object dt_fun2_dynamic_dynamic).
  intro H. inversion H. inversion H5. inversion H9. inversion H17. inversion H21.
Qed.

(* dynamic Function(dynamic Function(dynamic)) f = func<void Function(Object), dynamic>; // Yes *)
Goal TypeVoidnessPreserves dt_fun2_Object_void dt_fun2_dynamic_dynamic.
  unfold TypeVoidnessPreserves. simpl. auto 10.
Qed.

(* dynamic Function(dynamic Function(dynamic)) f = func<Object Function(Object), dynamic>; // Yes *)
Goal TypeVoidnessPreserves dt_fun2_Object_Object dt_fun2_dynamic_dynamic.
  unfold TypeVoidnessPreserves. simpl. auto.
Qed.

(* dynamic Function(Object Function(Object)) f = func<void Function(void), dynamic>; // No *)
Goal ~(TypeVoidnessPreserves dt_fun2_void_void dt_fun2_Object_Object).
  unfold not. intros. inversion H. inversion H5. inversion H9. inversion H17. inversion H21.
Qed.

(* dynamic Function(Object Function(Object)) f = func<dynamic Function(void), dynamic>; // No *)
Goal ~(TypeVoidnessPreserves dt_fun2_void_dynamic dt_fun2_Object_Object).
  unfold not. intros. inversion H. inversion H5. inversion H9. inversion H17. inversion H21.
Qed.

(* dynamic Function(Object Function(Object)) f = func<void Function(dynamic), dynamic>; // Yes *)
Goal TypeVoidnessPreserves dt_fun2_dynamic_void dt_fun2_Object_Object.
  unfold TypeVoidnessPreserves. simpl. auto.
Qed.

(* dynamic Function(Object Function(Object)) f = func<dynamic Function(dynamic), dynamic>; // Yes *)
Goal TypeVoidnessPreserves dt_fun2_dynamic_dynamic dt_fun2_Object_Object.
  unfold TypeVoidnessPreserves. simpl. auto.
Qed.
