; ModuleID = 'res/context_insensitive/c/global_struct/global_struct.bc'
source_filename = "res/context_insensitive/c/global_struct/global_struct.c"
target datalayout = "e-m:o-p270:32:32-p271:32:32-p272:64:64-i64:64-f80:128-n8:16:32:64-S128"
target triple = "x86_64-apple-macosx14.0.0"

%struct.my_struct = type { i32*, i32* }

@global_int = global i32 5, align 4
@struct_instance = global [2 x %struct.my_struct] [%struct.my_struct { i32* @global_int, i32* null }, %struct.my_struct { i32* null, i32* @global_int }], align 16

; Function Attrs: noinline nounwind optnone ssp uwtable
define i32 @main() #0 {
entry:
  %a = alloca i32, align 4
  %b = alloca i32, align 4
  %i = alloca i32, align 4
  store i32 1, i32* %a, align 4
  store i32 2, i32* %b, align 4
  store i32 0, i32* %i, align 4
  %0 = load i32, i32* %i, align 4
  %idxprom = sext i32 %0 to i64
  %arrayidx = getelementptr inbounds [2 x %struct.my_struct], [2 x %struct.my_struct]* @struct_instance, i64 0, i64 %idxprom
  %f1 = getelementptr inbounds %struct.my_struct, %struct.my_struct* %arrayidx, i32 0, i32 0
  store i32* %a, i32** %f1, align 16
  %1 = load i32, i32* %i, align 4
  %idxprom1 = sext i32 %1 to i64
  %arrayidx2 = getelementptr inbounds [2 x %struct.my_struct], [2 x %struct.my_struct]* @struct_instance, i64 0, i64 %idxprom1
  %f2 = getelementptr inbounds %struct.my_struct, %struct.my_struct* %arrayidx2, i32 0, i32 1
  store i32* %b, i32** %f2, align 8
  ret i32 0
}

attributes #0 = { noinline nounwind optnone ssp uwtable "frame-pointer"="all" "min-legal-vector-width"="0" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="penryn" "target-features"="+cx16,+cx8,+fxsr,+mmx,+sahf,+sse,+sse2,+sse3,+sse4.1,+ssse3,+x87" "tune-cpu"="generic" }

!llvm.module.flags = !{!0, !1, !2, !3}
!llvm.ident = !{!4}

!0 = !{i32 1, !"wchar_size", i32 4}
!1 = !{i32 7, !"PIC Level", i32 2}
!2 = !{i32 7, !"uwtable", i32 1}
!3 = !{i32 7, !"frame-pointer", i32 2}
!4 = !{!"Homebrew clang version 14.0.6"}
