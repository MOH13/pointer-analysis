; typedef struct
; {
;   int *f;
; } sub_st;
; 
; typedef struct
; {
;   int a;
;   sub_st b;
; } st;
; 
; int main()
; {
;   sub_st sub;
;   int e;
;   sub.f = &e;
;
;   st d;
;   // LLVM insertvalue code
; }

%struct.sub_st = type { i32* }
%struct.st = type { i32, %struct.sub_st }

define i32 @main() {
entry:
  %sub = alloca %struct.sub_st
  %e = alloca i32
  %d = alloca %struct.st
  %f = getelementptr inbounds %struct.sub_st, %struct.sub_st* %sub, i32 0, i32 0
  store i32* %e, i32** %f
  ; LLVM insertvalue code
  %dval = load %struct.st, %struct.st* %d
  %subval = load %struct.sub_st, %struct.sub_st* %sub
  %res = insertvalue %struct.st %dval, %struct.sub_st %subval, 1
  ret i32 0
}