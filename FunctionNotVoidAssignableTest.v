(* Copyright (c) 2017, the Dart project authors.  Please see the AUTHORS file
 * for details. All rights reserved. Use of this source code is governed by a
 * BSD-style license that can be found in the LICENSE file. *)

Require Import Utf8.
Require Import List.
Require Import ClassTestTypes.
Require Import NotVoidAssignability.

(* Simple function types *)
Definition dt_fun_void_void := dt_function dt_void (dt_void :: nil).
Definition dt_fun_void_dynamic := dt_function dt_dynamic (dt_void :: nil).
Definition dt_fun_dynamic_void := dt_function dt_void (dt_dynamic :: nil).
Definition dt_fun_dynamic_dynamic := dt_function dt_dynamic (dt_dynamic :: nil).
Definition dt_fun_Object_Object := dt_function dt_Object (dt_Object :: nil).
Definition dt_fun_Object_void := dt_function dt_void (dt_Object :: nil).
Definition dt_fun_void_Object := dt_function dt_Object (dt_void :: nil).

Hint Unfold
  cvt_Object vt_Object cvt_A_Object vt_A_Object cvt_A_1 vt_A_1
  cvt_A_A_1 vt_A_A_1 vt_fun_Object_nil vt_fun_A1_AA1 cvt_B_A1_Object
  vt_B_A1_Object cvt_B_ObjectObject vt_B_ObjectObject.

(* -------------------- Test cases from email -------------------- *)

(* A<Object> x = new A<void>(); // No *)
Goal NotVoidAssignable dt_A_void dt_A_Object.
  apply nva_class. unfold ct_A_void.
  apply nvact_upcast with (args1 := dt_void :: nil).
      apply dsscts_cons.
        apply dscts_first. apply dsct_args. apply dsp_cons.
          apply ds_Object.
        apply dsp_nil.
      apply dsscts_cons.
        apply dscts_rest. apply dscts_first. auto.
      apply dsscts_nil.
    apply ctn_first.
  apply nvap_cons_first. apply nva_base; discriminate.
Qed.

(* A<dynamic> x = new A<void>(); // Yes *)
Goal ~(NotVoidAssignable dt_A_void dt_A_dynamic).
  unfold not. intros. inversion H. inversion H2.
    subst. unfold ct_A_void in *.
    assert (args1 = dt_void :: nil).
      inversion H8.
        reflexivity.
      contradiction H6. reflexivity.
    subst args1. inversion H9.
      inversion H1. contradiction H10. reflexivity.
    inversion H1.
  unfold ct_A_dynamic in *.
  assert (args2 = dt_dynamic :: nil).
    inversion H8.
      reflexivity.
    contradiction H15. reflexivity.
  subst args2. inversion H9.
    inversion H11. apply H16. reflexivity.
  inversion H11.
Qed.

(* A<Object> x = new A<dynamic>(); // Yes *)
Goal ~(NotVoidAssignable dt_A_void dt_A_dynamic).
  unfold not. intros. inversion H. inversion H2; subst.
    unfold ct_A_void in *.
    assert (args1 = dt_void :: nil).
      inversion H8.
        reflexivity.
      contradiction H6. reflexivity.
    subst args1. inversion H9.
      inversion H1. apply H10. reflexivity.
    inversion H1.
  assert (args2 = dt_dynamic :: nil).
    inversion H8.
      reflexivity.
    contradiction H7. reflexivity.
  subst args2.
  inversion H9.
    inversion H1. apply H10. reflexivity.
  inversion H1.
Qed.

(* A<void> x = new A<dynamic>(); // voidV = dynamicV, yes *)
Goal ~(NotVoidAssignable dt_A_dynamic dt_A_void).
  unfold not. intros. inversion H. inversion H2; subst; unfold ct_A_dynamic in *.
    assert (args1 = dt_dynamic :: nil).
      inversion H8.
        reflexivity.
      contradiction H6. reflexivity.
    subst args1. inversion H9.
      inversion H1.
    inversion H1.
  assert (args2 = dt_void :: nil).
    inversion H8.
      reflexivity.
    contradiction H7. reflexivity.
  subst args2. inversion H9.
    inversion H1.
  inversion H1.
Qed.

(* A<void> x = new A<Object>(); // voidV = objectV, Yes *)
Goal ~(NotVoidAssignable dt_A_Object dt_A_void).
  unfold not. intros. inversion H. inversion H2; subst; unfold ct_A_Object in *.
    assert (args1 = dt_Object :: nil).
      inversion H8.
        reflexivity.
      contradiction H6. reflexivity.
    subst args1. inversion H9.
      inversion H1.
    inversion H1.
  assert (args2 = dt_void :: nil).
    inversion H8.
      reflexivity.
    contradiction H7. reflexivity.
  subst args2. inversion H9.
    inversion H1.
  inversion H1.
Qed.

(* dynamic x = new A<void>(); // Yes *)
Goal ~(NotVoidAssignable dt_A_void dt_dynamic).
  unfold not. intros. inversion H.
Qed.

(* Object x = new A<void>(); // Yes *)
Goal ~(NotVoidAssignable dt_A_void dt_Object).
  unfold not. intros. inversion H. inversion H2; subst; unfold ct_A_void in *.
    assert (args1 = nil).
      inversion H9.
    subst args1. inversion H9.
  inversion H8. inversion H10.
Qed.

(* Iterable<void> x = new List<void>(); // Yes *)
Goal ~(NotVoidAssignable dt_List_void dt_Iterable_void).
  unfold not. intros. inversion H. inversion H2; subst; unfold ct_List_void in *.
    assert (args1 = dt_void :: nil).
      inversion H8. inversion H10.
        reflexivity.
      inversion H17. inversion H24.
    subst args1. inversion H9.
      inversion H1. apply H6. reflexivity.
    inversion H1.
  inversion H8. inversion H10. inversion H17.
Qed.

(* List<void> x = new Iterable<void>(); // Yes *)
Goal ~(NotVoidAssignable dt_Iterable_void dt_List_void).
  unfold not. intros. inversion H. inversion H2; subst; unfold ct_Iterable_void in *.
    inversion H8. inversion H10. inversion H17.
  assert (args2 = dt_void :: nil).
    inversion H8. inversion H10.
      reflexivity.
    contradiction H16. reflexivity.
  subst args2. inversion H9.
    inversion H1. apply H7. reflexivity.
  inversion H1.
Qed.

(* Iterable<Object> x = new List<void>(); // No *)
Goal NotVoidAssignable dt_List_void dt_Iterable_Object.
  apply nva_class. apply nvact_upcast with (args1 := dt_void :: nil).
      apply dsscts_cons.
        apply dscts_rest. apply dscts_first. apply dsct_args. apply dsp_cons.
          auto.
        auto.
      apply dsscts_cons.
        apply dscts_rest. apply dscts_rest. apply dscts_first. auto.
      auto.
    apply ctn_rest.
      discriminate.
    apply ctn_first.
  apply nvap_cons_first. apply nva_base.
    discriminate.
  discriminate.
Qed.

(* List<Object> x = new Iterable<void>(); // No *)
Goal NotVoidAssignable dt_Iterable_void dt_List_Object.
  apply nva_class. apply nvact_downcast with (args2 := dt_Object :: nil).
      apply dsscts_cons.
        apply dscts_rest. apply dscts_first. apply dsct_args. auto.
      apply dsscts_cons.
        apply dscts_rest. apply dscts_rest. apply dscts_first. apply dsct_args. auto.
      auto.
    apply ctn_rest.
      discriminate.
    apply ctn_first.
  apply nvap_cons_first. apply nva_base.
    discriminate.
  discriminate.
Qed.

(* void Function(void) f = func<dynamic, dynamic>; // Yes!! void-to-dynamic is OK! *)
Goal ~(NotVoidAssignable dt_fun_dynamic_dynamic dt_fun_void_void).
  unfold not. intros. inversion H.
    inversion H2; subst; unfold dt_fun_dynamic_dynamic in *. inversion H5.
  inversion H5.
    inversion H7. apply H12. reflexivity.
  inversion H7.
Qed.

(* void Function(void) f = func<dynamic, void>; // Yes!! void-to-dynamic is OK! *)
Goal ~(NotVoidAssignable dt_fun_dynamic_void dt_fun_void_void).
  unfold not. intros. inversion H.
    inversion H2; subst; unfold dt_fun_dynamic_void in *.
    inversion H5. apply H0; reflexivity.
  inversion H5.
    inversion H7. apply H12. reflexivity.
  inversion H7.
Qed.

(* void Function(void) f = func<void, dynamic>; // Yes *)
Goal ~(NotVoidAssignable dt_fun_void_dynamic dt_fun_void_void).
  unfold not. intros. inversion H.
    inversion H2; subst; unfold dt_fun_void_dynamic in *.
    inversion H5.
  inversion H5.
    inversion H7. apply H11. reflexivity.
  inversion H7.
Qed.

(* void Function(void) f = func<Object, Object>; // No *)
Goal NotVoidAssignable dt_fun_Object_Object dt_fun_void_void.
  apply nva_function_arg.
    unfold DartAssignable. left. apply ds_function.
      apply ds_void.
    apply dsp_cons.
      apply ds_Object.
    auto.
  apply nvap_cons_first. apply nva_base.
    discriminate.
  discriminate.
Qed.

(* void Function(void) f = func<Object, void>; // No *)
Goal NotVoidAssignable dt_fun_Object_void dt_fun_void_void.
  apply nva_function_arg.
    unfold DartAssignable. left. apply ds_function.
      apply ds_void.
    apply dsp_cons.
      apply ds_Object.
    auto.
  apply nvap_cons_first. apply nva_base.
    discriminate.
  discriminate.
Qed.

(* void Function(void) f = func<void, Object>; // Yes *)
Goal ~(NotVoidAssignable dt_fun_void_Object dt_fun_void_void).
  unfold not. intros. inversion H.
    inversion H2; subst; unfold dt_fun_void_Object in *.
    inversion H5.
  inversion H5.
    inversion H7. apply H11. reflexivity.
  inversion H7.
Qed.

(* dynamic Function(dynamic) g = func<void, void>; // Yes *)
Goal ~(NotVoidAssignable dt_fun_void_void dt_fun_dynamic_dynamic).
  unfold not. intros. inversion H.
    inversion H3; subst; unfold dt_fun_void_void in *.
      inversion H5. apply H1. reflexivity.
    inversion H5. apply H1. reflexivity.
  inversion H5. inversion H7. inversion H7.
Qed.

(* dynamic Function(dynamic) g = func<dynamic, void>; // Yes *)
Goal ~(NotVoidAssignable dt_fun_dynamic_void dt_fun_dynamic_dynamic).
  unfold not. intros. inversion H.
    inversion H3; subst; unfold dt_fun_dynamic_void in *.
      inversion H5. apply H1. reflexivity.
    inversion H5. apply H1. reflexivity.
  inversion H5.
    inversion H7.
  inversion H7.
Qed.

(* dynamic Function(dynamic) g = func<void, dynamic>; // Yes *)
Goal ~(NotVoidAssignable dt_fun_void_dynamic dt_fun_dynamic_dynamic).
  unfold not. intros. inversion H.
    inversion H3; subst; unfold dt_fun_void_dynamic in *.
      inversion H5.
    inversion H5.
  inversion H5.
    inversion H7.
  inversion H7.
Qed.

(* dynamic Function(dynamic) g = func<Object, Object>; // Yes *)
Goal ~(NotVoidAssignable dt_fun_Object_Object dt_fun_dynamic_dynamic).
  unfold not. intros. inversion H.
    inversion H3; subst; unfold dt_fun_Object_Object in *.
      inversion H5.
    inversion H5.
  inversion H5.
    inversion H7. inversion H7.
Qed.

(* dynamic Function(dynamic) g = func<Object, void>; // Yes *)
Goal ~(NotVoidAssignable dt_fun_Object_void dt_fun_dynamic_dynamic).
  unfold not. intros. inversion H.
    inversion H3; subst; unfold dt_fun_Object_void in *.
      inversion H5. apply H1. reflexivity.
    inversion H5. apply H1. reflexivity.
  inversion H5.
    inversion H7.
  inversion H7.
Qed.

(* dynamic Function(dynamic) g = func<void, Object>; // Yes *)
Goal ~(NotVoidAssignable dt_fun_void_Object dt_fun_dynamic_dynamic).
  unfold not. intros. inversion H.
    inversion H3; subst; unfold dt_fun_void_Object in *.
      inversion H5.
    inversion H5.
  inversion H5.
    inversion H7.
  inversion H7.
Qed.

(* Object Function(Object) h = func<void, void>; // No *)
Goal NotVoidAssignable dt_fun_void_void dt_fun_Object_Object.
  apply nva_function_ret.
    unfold DartAssignable. left. apply ds_function.
      apply ds_Object.
    apply dsp_cons.
      apply ds_void.
    auto.
  apply nva_base; discriminate.
Qed.

(* Object Function(Object) h = func<dynamic, void>; // No *)
Goal NotVoidAssignable dt_fun_dynamic_void dt_fun_Object_Object.
  apply nva_function_ret.
    unfold DartAssignable. left. apply ds_function.
      apply ds_Object.
    apply dsp_cons.
      apply ds_dynamic.
    auto.
  apply nva_base; discriminate.
Qed.

(* Object Function(Object) h = func<void, dynamic>; // Yes *)
Goal ~(NotVoidAssignable dt_fun_void_dynamic dt_fun_Object_Object).
  unfold not. intros. inversion H.
    inversion H3; subst; unfold dt_fun_void_dynamic in *.
      inversion H5.
    inversion H5.
  inversion H5.
    inversion H7.
  inversion H7.
Qed.

(* Object Function(Object) h = func<Object, Object>; // Yes *)
Goal ~(NotVoidAssignable dt_fun_Object_Object dt_fun_Object_Object).
  unfold not. intros. inversion H.
    inversion H3; subst; unfold dt_fun_Object_Object in *.
      inversion H5. inversion H2.
        inversion H12.
      inversion H12; subst.
    inversion H5. inversion H2.
      inversion H12.
    inversion H12.
  inversion H5.
    inversion H7. inversion H13.
      inversion H20.
    inversion H20.
  inversion H7.
Qed.

(* Object Function(Object) h = func<Object, void>; // No *)
Goal NotVoidAssignable dt_fun_Object_void dt_fun_Object_Object.
  apply nva_function_ret.
    unfold DartAssignable. left. apply ds_function.
      apply ds_Object.
    apply dsp_cons.
      apply ds_Object.
    auto.
  apply nva_base; discriminate.
Qed.

(* Object Function(Object) h = func<void, Object>; // Yes *)
Goal ~(NotVoidAssignable dt_fun_void_Object dt_fun_Object_Object).
  unfold not. intros. inversion H.
    inversion H3; subst; unfold dt_fun_void_Object in *.
      inversion H5. inversion H2.
        inversion H12.
      inversion H12.
    inversion H5. inversion H2.
      inversion H12.
    inversion H12.
  inversion H5.
    inversion H7.
  inversion H7.
Qed.

Goal NotVoidAssignable dt_fun_Object_Object dt_fun_void_Object. (* TODO: different from VoidnessType result *)
  apply nva_function_arg.
    unfold DartAssignable. left. apply ds_function.
      apply ds_Object.
    apply dsp_cons.
      apply ds_Object.
    auto.
  apply nvap_cons_first. apply nva_base; discriminate.
Qed.
