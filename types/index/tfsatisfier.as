#include "aldor"
#include "aldorio"
#pile
import from SpadTypeLib
inline from SpadTypeLib

import from BooleanFold, List TForm

SimpleTypeSystem: with
    typeSystem: () -> TypeSystem
== add
    typeSystem(): TypeSystem ==
        import from FnSatisfier
        infer(ab: AnnotatedAbSyn): TForm == infer(satisfier$SimpleSatisfier::FnSatisfier, ab)$TypePackage
        create(infer)$TypeSystem

SimpleSatisfier: with
--    apply: (%, TForm, TForm) -> Partial SatResult
    satisfier: (TForm, TForm) -> SatResult
== add
    import from SatResult, TypePackage
    SatisfierRule ==> (TForm, TForm) -> Partial SatResult

    local allSatType(S: TForm, T: TForm): Partial SatResult ==
        import from TfType, TfMulti
        stdout << "all sat type " << theType? T << " " << multi? S << newline
        not theType? T => failed
        multi? S => [failed()]
        [success()]

    local domainSat(S: TForm, T: TForm): Partial SatResult ==
        import from List Export
        not isCategory? S => failed
        not isCategory? T => failed
        true => [success()]
        stdout << "(DomainSat: " << S << " && " << T << newline
        parentsS := allCatParents S
        parentsT := allCatParents T
        stdout << "ParentS: " << parentsS << newline
        stdout << "ParentT: " << parentsT << newline
        res := if _and/(member?(parentT, parentsS) for parentT in parentsT) then [success()] else [failed()]
        stdout << "DomainSat: " << res << ")" << newline
        res

    local declareSatRHS(S: TForm, T: TForm): Partial SatResult ==
        import from TfDeclare
        not declare? T => failed
        [satisfier(S, type(T::TfDeclare))]

    local declareSatLHS(S: TForm, T: TForm): Partial SatResult ==
        import from TfDeclare
        not declare? S => failed
        [satisfier(type(S::TfDeclare), T)]

    local isCategory?(tf: TForm): Boolean ==
        import from Symbol
        stdout << "isCategory? " << tf << " " << category? tf << " general? tf = " << general? tf << " id tf = " << id tf << newline
        import from TfCategory, TfGeneral
        category? tf => true
        general? tf => isSyntaxCategory(tf)
        false

    local isSyntaxCategory(tf: TForm): Boolean ==
        import from TfGeneral, TfDeclare, TfCatType
        type := modDeclare type(tf::TfGeneral)
        stdout << "Type of cat: " << type << newline
        catType? type

    local multiSat(S: TForm, T: TForm): Partial SatResult ==
        import from TfMulti, MachineInteger
        not multi? S => failed
        not multi? T => failed
        # parts(S::TfMulti) ~= # parts(T::TfMulti) => [failed()]
        if _and/(success? satisfier(Sn, Tn) for Sn in parts(S::TfMulti) for Tn in parts(T::TfMulti)) then [success()] else [failed()]

    local defaultSat(S: TForm, T: TForm): Partial SatResult ==
        stdout << "No applicable rules for " << S << " and " << T << newline
        failed

    local SatisfierRules: List SatisfierRule == [
        declareSatLHS,
        declareSatRHS,
        allSatType,
        domainSat,
        multiSat,
        defaultSat
    ]

    local satisfierX(S: TForm, T: TForm): SatResult ==
        import from List SatisfierRule
        for satrule in SatisfierRules repeat
            r: Partial SatResult := satrule(S, T)
            not failed? r => return retract r
        failed()

    satisfier(S: TForm, T: TForm): SatResult ==
        import from Symbol
        stdout << "(Sat " << id S << " " << id T << newline
        r := satisfierX(S, T)
        stdout << " Sat: " << r << ")" << newline
        r
