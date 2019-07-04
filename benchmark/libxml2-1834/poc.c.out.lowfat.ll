; ModuleID = '../../poc.c'
source_filename = "../../poc.c"
target datalayout = "e-m:e-i64:64-f80:128-n8:16:32:64-S128"
target triple = "x86_64-unknown-linux-gnu"

%LOWFAT_GLOBAL_WRAPPER = type <{ [32 x i8], [32 x i8] }>
%LOWFAT_GLOBAL_WRAPPER.0 = type <{ [1 x i8], [31 x i8] }>

@LOWFAT_GLOBAL_WRAPPER_.str = private global %LOWFAT_GLOBAL_WRAPPER <{ [32 x i8] zeroinitializer, [32 x i8] c"Normal string allocation error\0A\00" }>, section "lowfat_section_64", align 64
@LOWFAT_GLOBAL_WRAPPER_.str.1 = private global %LOWFAT_GLOBAL_WRAPPER.0 <{ [1 x i8] zeroinitializer, [31 x i8] c"Large string allocation error\0A\00" }>, section "lowfat_section_32", align 32

; Function Attrs: noinline nounwind uwtable
define i8* @getNormalStr() #0 !dbg !14 {
  %1 = call noalias i8* @lowfat_malloc(i64 20) #6, !dbg !17
  call void @llvm.dbg.value(metadata i8* %1, i64 0, metadata !18, metadata !19), !dbg !20
  %2 = icmp eq i8* %1, null, !dbg !21
  br i1 %2, label %3, label %5, !dbg !23

; <label>:3:                                      ; preds = %0
  %4 = call i32 (i8*, ...) @printf(i8* getelementptr inbounds (%LOWFAT_GLOBAL_WRAPPER, %LOWFAT_GLOBAL_WRAPPER* @LOWFAT_GLOBAL_WRAPPER_.str, i32 0, i32 1, i32 0)), !dbg !24
  call void @exit(i32 1) #7, !dbg !26
  unreachable, !dbg !26

; <label>:5:                                      ; preds = %0
  call void @llvm.memset.p0i8.i64(i8* %1, i8 65, i64 19, i32 1, i1 false), !dbg !27
  %6 = getelementptr inbounds i8, i8* %1, i64 19, !dbg !28
  store i8 0, i8* %6, align 1, !dbg !29
  ret i8* %1, !dbg !30
}

; Function Attrs: nounwind readnone
declare void @llvm.dbg.declare(metadata, metadata, metadata) #1

; Function Attrs: nounwind
declare noalias i8* @malloc(i64) #2

declare i32 @printf(i8*, ...) #3

; Function Attrs: noreturn nounwind
declare void @exit(i32) #4

; Function Attrs: argmemonly nounwind
declare void @llvm.memset.p0i8.i64(i8* nocapture writeonly, i8, i64, i32, i1) #5

; Function Attrs: noinline nounwind uwtable
define i8* @getLongStr() #0 !dbg !31 {
  %1 = call noalias i8* @lowfat_malloc(i64 4294967294) #6, !dbg !32
  call void @llvm.dbg.value(metadata i8* %1, i64 0, metadata !33, metadata !19), !dbg !34
  %2 = icmp eq i8* %1, null, !dbg !35
  br i1 %2, label %3, label %5, !dbg !37

; <label>:3:                                      ; preds = %0
  %4 = call i32 (i8*, ...) @printf(i8* getelementptr inbounds (%LOWFAT_GLOBAL_WRAPPER.0, %LOWFAT_GLOBAL_WRAPPER.0* @LOWFAT_GLOBAL_WRAPPER_.str.1, i32 0, i32 1, i32 0)), !dbg !38
  call void @exit(i32 1) #7, !dbg !40
  unreachable, !dbg !40

; <label>:5:                                      ; preds = %0
  call void @llvm.memset.p0i8.i64(i8* %1, i8 65, i64 4294967293, i32 1, i1 false), !dbg !41
  %6 = getelementptr inbounds i8, i8* %1, i64 4294967293, !dbg !42
  store i8 0, i8* %6, align 1, !dbg !43
  ret i8* %1, !dbg !44
}

; Function Attrs: noinline nounwind uwtable
define void @crash() #0 !dbg !45 {
  %1 = call i8* @getLongStr(), !dbg !48
  %2 = call i8* @getNormalStr(), !dbg !49
  %3 = call i8* @xmlStrcat(i8* %1, i8* %2), !dbg !51
  ret void, !dbg !53
}

declare i8* @xmlStrcat(i8*, i8*) #3

; Function Attrs: noinline nounwind uwtable
define i32 @main(i32, i8**) #0 !dbg !54 {
  call void @llvm.dbg.value(metadata i32 %0, i64 0, metadata !59, metadata !19), !dbg !60
  call void @llvm.dbg.value(metadata i8** %1, i64 0, metadata !61, metadata !19), !dbg !62
  call void @crash(), !dbg !63
  ret i32 0, !dbg !64
}

; Function Attrs: nounwind readnone
declare void @llvm.dbg.value(metadata, i64, metadata, metadata) #1

; Function Attrs: nounwind
declare noalias nonnull i8* @lowfat_malloc(i64) #6

attributes #0 = { noinline nounwind uwtable "correctly-rounded-divide-sqrt-fp-math"="false" "disable-tail-calls"="false" "less-precise-fpmad"="false" "no-frame-pointer-elim"="true" "no-frame-pointer-elim-non-leaf" "no-infs-fp-math"="false" "no-jump-tables"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "no-trapping-math"="false" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+bmi,+bmi2,+fxsr,+lzcnt,+mmx,+sse,+sse2,+x87" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #1 = { nounwind readnone }
attributes #2 = { nounwind "correctly-rounded-divide-sqrt-fp-math"="false" "disable-tail-calls"="false" "less-precise-fpmad"="false" "no-frame-pointer-elim"="true" "no-frame-pointer-elim-non-leaf" "no-infs-fp-math"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "no-trapping-math"="false" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+bmi,+bmi2,+fxsr,+lzcnt,+mmx,+sse,+sse2,+x87" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #3 = { "correctly-rounded-divide-sqrt-fp-math"="false" "disable-tail-calls"="false" "less-precise-fpmad"="false" "no-frame-pointer-elim"="true" "no-frame-pointer-elim-non-leaf" "no-infs-fp-math"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "no-trapping-math"="false" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+bmi,+bmi2,+fxsr,+lzcnt,+mmx,+sse,+sse2,+x87" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #4 = { noreturn nounwind "correctly-rounded-divide-sqrt-fp-math"="false" "disable-tail-calls"="false" "less-precise-fpmad"="false" "no-frame-pointer-elim"="true" "no-frame-pointer-elim-non-leaf" "no-infs-fp-math"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "no-trapping-math"="false" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+bmi,+bmi2,+fxsr,+lzcnt,+mmx,+sse,+sse2,+x87" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #5 = { argmemonly nounwind }
attributes #6 = { nounwind }
attributes #7 = { noreturn nounwind }

!llvm.dbg.cu = !{!0}
!llvm.module.flags = !{!11, !12}
!llvm.ident = !{!13}

!0 = distinct !DICompileUnit(language: DW_LANG_C99, file: !1, producer: "clang version 4.0.0 (tags/RELEASE_400/final)", isOptimized: false, runtimeVersion: 0, emissionKind: FullDebug, enums: !2, retainedTypes: !3)
!1 = !DIFile(filename: "../../poc.c", directory: "/home/gaoxiang/project/crash-free-fix/benchmark/libxml2-1834/project/klee")
!2 = !{}
!3 = !{!4, !6, !7}
!4 = !DIDerivedType(tag: DW_TAG_pointer_type, baseType: !5, size: 64)
!5 = !DIBasicType(name: "char", size: 8, encoding: DW_ATE_signed_char)
!6 = !DIDerivedType(tag: DW_TAG_pointer_type, baseType: null, size: 64)
!7 = !DIDerivedType(tag: DW_TAG_pointer_type, baseType: !8, size: 64)
!8 = !DIDerivedType(tag: DW_TAG_typedef, name: "xmlChar", file: !9, line: 28, baseType: !10)
!9 = !DIFile(filename: "../include/libxml/xmlstring.h", directory: "/home/gaoxiang/project/crash-free-fix/benchmark/libxml2-1834/project/klee")
!10 = !DIBasicType(name: "unsigned char", size: 8, encoding: DW_ATE_unsigned_char)
!11 = !{i32 2, !"Dwarf Version", i32 4}
!12 = !{i32 2, !"Debug Info Version", i32 3}
!13 = !{!"clang version 4.0.0 (tags/RELEASE_400/final)"}
!14 = distinct !DISubprogram(name: "getNormalStr", scope: !1, file: !1, line: 9, type: !15, isLocal: false, isDefinition: true, scopeLine: 9, isOptimized: false, unit: !0, variables: !2)
!15 = !DISubroutineType(types: !16)
!16 = !{!4}
!17 = !DILocation(line: 10, column: 25, scope: !14)
!18 = !DILocalVariable(name: "str", scope: !14, file: !1, line: 10, type: !4)
!19 = !DIExpression()
!20 = !DILocation(line: 10, column: 11, scope: !14)
!21 = !DILocation(line: 11, column: 12, scope: !22)
!22 = distinct !DILexicalBlock(scope: !14, file: !1, line: 11, column: 8)
!23 = !DILocation(line: 11, column: 8, scope: !14)
!24 = !DILocation(line: 12, column: 9, scope: !25)
!25 = distinct !DILexicalBlock(scope: !22, file: !1, line: 11, column: 20)
!26 = !DILocation(line: 13, column: 9, scope: !25)
!27 = !DILocation(line: 15, column: 5, scope: !14)
!28 = !DILocation(line: 16, column: 5, scope: !14)
!29 = !DILocation(line: 16, column: 25, scope: !14)
!30 = !DILocation(line: 17, column: 5, scope: !14)
!31 = distinct !DISubprogram(name: "getLongStr", scope: !1, file: !1, line: 20, type: !15, isLocal: false, isDefinition: true, scopeLine: 20, isOptimized: false, unit: !0, variables: !2)
!32 = !DILocation(line: 21, column: 25, scope: !31)
!33 = !DILocalVariable(name: "str", scope: !31, file: !1, line: 21, type: !4)
!34 = !DILocation(line: 21, column: 11, scope: !31)
!35 = !DILocation(line: 22, column: 12, scope: !36)
!36 = distinct !DILexicalBlock(scope: !31, file: !1, line: 22, column: 8)
!37 = !DILocation(line: 22, column: 8, scope: !31)
!38 = !DILocation(line: 23, column: 9, scope: !39)
!39 = distinct !DILexicalBlock(scope: !36, file: !1, line: 22, column: 20)
!40 = !DILocation(line: 24, column: 9, scope: !39)
!41 = !DILocation(line: 26, column: 5, scope: !31)
!42 = !DILocation(line: 27, column: 5, scope: !31)
!43 = !DILocation(line: 27, column: 25, scope: !31)
!44 = !DILocation(line: 28, column: 5, scope: !31)
!45 = distinct !DISubprogram(name: "crash", scope: !1, file: !1, line: 32, type: !46, isLocal: false, isDefinition: true, scopeLine: 32, isOptimized: false, unit: !0, variables: !2)
!46 = !DISubroutineType(types: !47)
!47 = !{null}
!48 = !DILocation(line: 33, column: 26, scope: !45)
!49 = !DILocation(line: 33, column: 51, scope: !50)
!50 = !DILexicalBlockFile(scope: !45, file: !1, discriminator: 1)
!51 = !DILocation(line: 33, column: 5, scope: !52)
!52 = !DILexicalBlockFile(scope: !45, file: !1, discriminator: 2)
!53 = !DILocation(line: 34, column: 1, scope: !45)
!54 = distinct !DISubprogram(name: "main", scope: !1, file: !1, line: 36, type: !55, isLocal: false, isDefinition: true, scopeLine: 36, flags: DIFlagPrototyped, isOptimized: false, unit: !0, variables: !2)
!55 = !DISubroutineType(types: !56)
!56 = !{!57, !57, !58}
!57 = !DIBasicType(name: "int", size: 32, encoding: DW_ATE_signed)
!58 = !DIDerivedType(tag: DW_TAG_pointer_type, baseType: !4, size: 64)
!59 = !DILocalVariable(name: "argc", arg: 1, scope: !54, file: !1, line: 36, type: !57)
!60 = !DILocation(line: 36, column: 14, scope: !54)
!61 = !DILocalVariable(name: "argv", arg: 2, scope: !54, file: !1, line: 36, type: !58)
!62 = !DILocation(line: 36, column: 27, scope: !54)
!63 = !DILocation(line: 37, column: 5, scope: !54)
!64 = !DILocation(line: 38, column: 5, scope: !54)
