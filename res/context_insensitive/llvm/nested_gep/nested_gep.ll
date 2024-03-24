; C-code:
;
; typedef struct
; {
;   int *f1;
;   int *f2;
; } my_struct;
;
; int global_int = 5
; my_struct_t struct_instance[1] = {{.f1 = 0, .f2 = &global_int}}
;
; int main()
; {
;   int a = 1;
;   struct_instance[0].f2 = &a;
;   return 0;
; }
;

%struct.my_struct = type { i32*, i32* }

@global_int = global i32 5, align 4
@struct_instance = global [1 x %struct.my_struct] [%struct.my_struct { i32* null, i32* @global_int }], align 16

define i32 @main() {
entry:
  %a = alloca i32, align 4
  %i = alloca i32, align 4
  store i32 1, i32* %a, align 4
  store i32 0, i32* %i, align 4
  %idx = load i32, i32* %i, align 4
  %f2 = getelementptr inbounds [1 x %struct.my_struct], [1 x %struct.my_struct]* @struct_instance, i32 0, i32 %idx, i32 1
  store i32* %a, i32** %f2, align 16
  ret i32 0
}
