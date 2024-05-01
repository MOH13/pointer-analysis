; ModuleID = 'res/context_insensitive/c/array_of_structs/nested_structs.bc'
source_filename = "res/context_insensitive/c/array_of_structs/nested_structs.c"
target datalayout = "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-f80:128-n8:16:32:64-S128"
target triple = "x86_64-pc-linux-gnu"

%struct.nested = type { %struct.anon, [10 x %struct.anon.0] }
%struct.anon = type { i32, i32 }
%struct.anon.0 = type { i32*, %struct.simple }
%struct.simple = type { i32* }

; Function Attrs: noinline nounwind optnone uwtable
define dso_local i32 @main() #0 {
entry:
  %x = alloca i32, align 4
  %a = alloca %struct.nested, align 8
  %ap = alloca %struct.nested*, align 8
  %q = alloca i32*, align 8
  store i32 0, i32* %x, align 4
  %f2 = getelementptr inbounds %struct.nested, %struct.nested* %a, i32 0, i32 1
  %arrayidx = getelementptr inbounds [10 x %struct.anon.0], [10 x %struct.anon.0]* %f2, i64 0, i64 7
  %f21 = getelementptr inbounds %struct.anon.0, %struct.anon.0* %arrayidx, i32 0, i32 0
  store i32* %x, i32** %f21, align 8
  store %struct.nested* %a, %struct.nested** %ap, align 8
  %0 = load %struct.nested*, %struct.nested** %ap, align 8
  %f22 = getelementptr inbounds %struct.nested, %struct.nested* %0, i32 0, i32 1
  %arrayidx3 = getelementptr inbounds [10 x %struct.anon.0], [10 x %struct.anon.0]* %f22, i64 0, i64 7
  %f214 = getelementptr inbounds %struct.anon.0, %struct.anon.0* %arrayidx3, i32 0, i32 0
  %1 = load i32*, i32** %f214, align 8
  %2 = load %struct.nested*, %struct.nested** %ap, align 8
  %f25 = getelementptr inbounds %struct.nested, %struct.nested* %2, i32 0, i32 1
  %arrayidx6 = getelementptr inbounds [10 x %struct.anon.0], [10 x %struct.anon.0]* %f25, i64 0, i64 7
  %f227 = getelementptr inbounds %struct.anon.0, %struct.anon.0* %arrayidx6, i32 0, i32 1
  %field = getelementptr inbounds %struct.simple, %struct.simple* %f227, i32 0, i32 0
  store i32* %1, i32** %field, align 8
  %3 = load %struct.nested*, %struct.nested** %ap, align 8
  %f28 = getelementptr inbounds %struct.nested, %struct.nested* %3, i32 0, i32 1
  %arrayidx9 = getelementptr inbounds [10 x %struct.anon.0], [10 x %struct.anon.0]* %f28, i64 0, i64 7
  %f2210 = getelementptr inbounds %struct.anon.0, %struct.anon.0* %arrayidx9, i32 0, i32 1
  %field11 = getelementptr inbounds %struct.simple, %struct.simple* %f2210, i32 0, i32 0
  %4 = load i32*, i32** %field11, align 8
  store i32* %4, i32** %q, align 8
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
