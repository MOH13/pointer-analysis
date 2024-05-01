; ModuleID = 'res/context_insensitive/c/test4/test4.bc'
source_filename = "res/context_insensitive/c/test4/test4.c"
target datalayout = "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-f80:128-n8:16:32:64-S128"
target triple = "x86_64-pc-linux-gnu"

; Function Attrs: noinline nounwind optnone uwtable
define dso_local i32* @id(i32* noundef %p) #0 {
entry:
  %p.addr = alloca i32*, align 8
  %x = alloca i32, align 4
  store i32* %p, i32** %p.addr, align 8
  store i32 2, i32* %x, align 4
  %0 = load i32*, i32** %p.addr, align 8
  ret i32* %0
}

; Function Attrs: noinline nounwind optnone uwtable
define dso_local i32 @main() #0 {
entry:
  %x = alloca i32, align 4
  %p = alloca i32*, align 8
  %q = alloca i32*, align 8
  store i32 1, i32* %x, align 4
  store i32* %x, i32** %p, align 8
  %0 = load i32*, i32** %p, align 8
  %call = call i32* @id(i32* noundef %0)
  store i32* %call, i32** %q, align 8
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
