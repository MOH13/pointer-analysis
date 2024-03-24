; C-code:
;
; typedef struct
; {
;   int *a;
;   int b;
; } st;
;
; int main()
; {
;   st d[1];
;   int e;
;   d[0].a = &e;
;
;   // LLVM extract value code
;  
; }
;

%struct.st = type { i32*, i32 }

define i32 @main() {
entry:
  %d = alloca [1 x %struct.st]
  %e = alloca i32
  %arrayidx = getelementptr inbounds [1 x %struct.st], [1 x %struct.st]* %d, i64 0, i64 0
  %a = getelementptr inbounds %struct.st, %struct.st* %arrayidx, i32 0, i32 0
  store i32* %e, i32** %a
  ; LLVM extract value code
  %dval = load [1 x %struct.st], [1 x %struct.st]* %d
  %f = extractvalue [1 x %struct.st] %dval, 0
  ret i32 0
}