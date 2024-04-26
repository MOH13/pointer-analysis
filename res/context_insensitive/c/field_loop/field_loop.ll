; ModuleID = 'res/context_insensitive/c/field_loop/field_loop.bc'
source_filename = "res/context_insensitive/c/field_loop/field_loop.c"
target datalayout = "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-f80:128-n8:16:32:64-S128"
target triple = "x86_64-pc-linux-gnu"

%struct.aggr = type { i32*, i32* }

; Function Attrs: noinline nounwind optnone uwtable
define dso_local i32 @main() #0 {
entry:
  %a = alloca %struct.aggr, align 8
  %p = alloca %struct.aggr*, align 8
  %q = alloca i8*, align 8
  %0 = bitcast %struct.aggr* %a to i8*
  store i8* %0, i8** %q, align 8
  %1 = load i8*, i8** %q, align 8
  %2 = bitcast i8* %1 to %struct.aggr*
  store %struct.aggr* %2, %struct.aggr** %p, align 8
  %3 = load %struct.aggr*, %struct.aggr** %p, align 8
  %f2 = getelementptr inbounds %struct.aggr, %struct.aggr* %3, i32 0, i32 1
  %4 = bitcast i32** %f2 to i8*
  store i8* %4, i8** %q, align 8
  ret i32 0
}

attributes #0 = { noinline nounwind optnone uwtable "frame-pointer"="all" "min-legal-vector-width"="0" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+cx8,+fxsr,+mmx,+sse,+sse2,+x87" "tune-cpu"="generic" }

!llvm.module.flags = !{!0, !1, !2, !3, !4}
!llvm.ident = !{!5}

!0 = !{i32 1, !"wchar_size", i32 4}
!1 = !{i32 7, !"PIC Level", i32 2}
!2 = !{i32 7, !"PIE Level", i32 2}
!3 = !{i32 7, !"uwtable", i32 1}
!4 = !{i32 7, !"frame-pointer", i32 2}
!5 = !{!"Ubuntu clang version 14.0.0-1ubuntu1.1"}
