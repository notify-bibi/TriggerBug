; ModuleID = 'const.c'
source_filename = "const.c"
target datalayout = "e-m:w-p270:32:32-p271:32:32-p272:64:64-i64:64-f80:128-n8:16:32:64-S128"
target triple = "x86_64-pc-windows-msvc19.30.30423"

; Function Attrs: noinline nounwind uwtable
define dso_local i32 @ff(i32 %argn) #0 {
entry:
  %argn.addr = alloca i32, align 4
  %c1 = alloca i32, align 4
  %c2 = alloca i32, align 4
  %c3 = alloca i32, align 4
  store i32 %argn, i32* %argn.addr, align 4
  %0 = load i32, i32* %argn.addr, align 4
  store i32 %0, i32* %c1, align 4
  store i32 8, i32* %c2, align 4
  %1 = load i32, i32* %c1, align 4
  %2 = load i32, i32* %c2, align 4
  %add = add nsw i32 %1, %2
  store i32 %add, i32* %c3, align 4
  %3 = load i32, i32* %c3, align 4
  ret i32 %3
}

attributes #0 = { noinline nounwind uwtable "correctly-rounded-divide-sqrt-fp-math"="false" "disable-tail-calls"="false" "frame-pointer"="none" "less-precise-fpmad"="false" "min-legal-vector-width"="0" "no-infs-fp-math"="false" "no-jump-tables"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "no-trapping-math"="false" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+cx8,+fxsr,+mmx,+sse,+sse2,+x87" "unsafe-fp-math"="false" "use-soft-float"="false" }

!llvm.module.flags = !{!0, !1}
!llvm.ident = !{!2}

!0 = !{i32 1, !"wchar_size", i32 2}
!1 = !{i32 7, !"PIC Level", i32 2}
!2 = !{!"clang version 10.0.1 "}
