; ModuleID = 'const.c'
source_filename = "const.c"
target datalayout = "e-m:w-p270:32:32-p271:32:32-p272:64:64-i64:64-f80:128-n8:16:32:64-S128"
target triple = "x86_64-pc-windows-msvc19.30.30423"

%struct.df = type { i32, i32, i32 }

; Function Attrs: noinline nounwind optnone uwtable
define dso_local i32 @ff(%struct.df* %i, i32 %argn) #0 {
entry:
  %argn.addr = alloca i32, align 4
  %i.addr = alloca %struct.df*, align 8
  %v = alloca %struct.df, align 4
  %c1 = alloca i32, align 4
  %c2 = alloca i32, align 4
  %c3 = alloca i32, align 4
  store i32 %argn, i32* %argn.addr, align 4
  store %struct.df* %i, %struct.df** %i.addr, align 8
  %0 = load %struct.df*, %struct.df** %i.addr, align 8
  %1 = bitcast %struct.df* %v to i8*
  %2 = bitcast %struct.df* %0 to i8*
  call void @llvm.memcpy.p0i8.p0i8.i64(i8* align 4 %1, i8* align 4 %2, i64 12, i1 false)
  %a = getelementptr inbounds %struct.df, %struct.df* %v, i32 0, i32 0
  %3 = load i32, i32* %a, align 4
  %and = and i32 %3, 255
  store i32 %and, i32* %c1, align 4
  %c = getelementptr inbounds %struct.df, %struct.df* %v, i32 0, i32 2
  %4 = load i32, i32* %c, align 4
  store i32 %4, i32* %c2, align 4
  %5 = load i32, i32* %c1, align 4
  %6 = load i32, i32* %c2, align 4
  %add = add nsw i32 %5, %6
  store i32 %add, i32* %c3, align 4
  %7 = load i32, i32* %c3, align 4
  %conv = trunc i32 %7 to i8
  %c4 = getelementptr inbounds %struct.df, %struct.df* %v, i32 0, i32 2
  %8 = bitcast i32* %c4 to i8*
  %arrayidx = getelementptr inbounds i8, i8* %8, i64 1
  store i8 %conv, i8* %arrayidx, align 1
  %9 = load %struct.df*, %struct.df** %i.addr, align 8
  %10 = bitcast %struct.df* %9 to i8*
  %11 = bitcast %struct.df* %v to i8*
  call void @llvm.memcpy.p0i8.p0i8.i64(i8* align 4 %10, i8* align 4 %11, i64 12, i1 false)
  %12 = load i32, i32* %c3, align 4
  ret i32 %12
}

; Function Attrs: argmemonly nounwind willreturn
declare void @llvm.memcpy.p0i8.p0i8.i64(i8* noalias nocapture writeonly, i8* noalias nocapture readonly, i64, i1 immarg) #1

attributes #0 = { noinline nounwind optnone uwtable "correctly-rounded-divide-sqrt-fp-math"="false" "disable-tail-calls"="false" "frame-pointer"="none" "less-precise-fpmad"="false" "min-legal-vector-width"="0" "no-infs-fp-math"="false" "no-jump-tables"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "no-trapping-math"="false" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+cx8,+fxsr,+mmx,+sse,+sse2,+x87" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #1 = { argmemonly nounwind willreturn }

!llvm.module.flags = !{!0, !1}
!llvm.ident = !{!2}

!0 = !{i32 1, !"wchar_size", i32 2}
!1 = !{i32 7, !"PIC Level", i32 2}
!2 = !{!"clang version 10.0.1 "}
