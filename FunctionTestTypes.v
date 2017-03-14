Require Import Utf8.
Require Import Types.
Require Import List.

(* Object *)
Definition ct_Object : ClassTypes := (Object, nil) :: nil.
Definition dt_Object := dt_class ct_Object.

(* Function types *)
Definition dt_fun_void_void := dt_function dt_void (dt_void :: nil).
Definition dt_fun_void_dynamic := dt_function dt_dynamic (dt_void :: nil).
Definition dt_fun_void_Object := dt_function dt_Object (dt_void :: nil).
Definition dt_fun_dynamic_void := dt_function dt_void (dt_dynamic :: nil).
Definition dt_fun_dynamic_dynamic := dt_function dt_dynamic (dt_dynamic :: nil).
Definition dt_fun_dynamic_Object := dt_function dt_Object (dt_dynamic :: nil).
Definition dt_fun_Object_Object := dt_function dt_Object (dt_Object :: nil).
Definition dt_fun_Object_void := dt_function dt_void (dt_Object :: nil).
Definition dt_fun_Object_dynamic := dt_function dt_dynamic (dt_Object :: nil).
Definition dt_fun2_void_void := dt_function dt_dynamic (dt_fun_void_void :: nil).
Definition dt_fun2_void_dynamic := dt_function dt_dynamic (dt_fun_void_dynamic :: nil).
Definition dt_fun2_void_Object := dt_function dt_dynamic (dt_fun_void_Object :: nil).
Definition dt_fun2_dynamic_void := dt_function dt_dynamic (dt_fun_dynamic_void :: nil).
Definition dt_fun2_dynamic_dynamic := dt_function dt_dynamic (dt_fun_dynamic_dynamic :: nil).
Definition dt_fun2_dynamic_Object := dt_function dt_dynamic (dt_fun_dynamic_Object :: nil).
Definition dt_fun2_Object_void := dt_function dt_dynamic (dt_fun_Object_void :: nil).
Definition dt_fun2_Object_dynamic := dt_function dt_dynamic (dt_fun_Object_dynamic :: nil).
Definition dt_fun2_Object_Object := dt_function dt_dynamic (dt_fun_Object_Object :: nil).

Hint Unfold
  ct_Object dt_Object
  dt_fun_void_void dt_fun_void_dynamic dt_fun_void_Object
  dt_fun_dynamic_void dt_fun_dynamic_dynamic dt_fun_dynamic_Object
  dt_fun_Object_Object dt_fun_Object_void dt_fun_Object_dynamic
  dt_fun2_void_void dt_fun2_void_dynamic dt_fun2_void_Object
  dt_fun2_dynamic_void dt_fun2_dynamic_dynamic dt_fun2_dynamic_Object
  dt_fun2_Object_void dt_fun2_Object_dynamic dt_fun2_Object_Object.
