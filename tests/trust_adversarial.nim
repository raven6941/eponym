## Issue #544: adversarial trust-attribution regression tests.
##
## Each channel probes whether `definitionTrustLines` (codegen.nim) reports
## trust honestly. Channels 1, 3, 4 assert the report IS complete.
## Channel 2 documents a known limitation (syntactic type-name collection):
## the test asserts the current behavior so the limitation cannot regress
## silently; see the follow-up issue for the reduction-aware fix.
import std/[macros, os, sets, tables]
import eponym_embed
import elab
import codegen

const probeDir = "tests/trust_adversarial"

proc findDef(defs: seq[ElabDef], name: string): ElabDef {.compileTime.} =
  for d in defs:
    if d.name == name:
      return d
  raise newException(ValueError, "definition not found: " & name)

proc trustFor(checked: tuple[defs: seq[ElabDef], globals: Globals,
                            allDefs: seq[ElabDef]], defName: string,
             declared: HashSet[string], postulateTrust: Table[string, string],
             runtimeTypes: seq[HostRuntimeType]): seq[string] {.compileTime.} =
  let d = findDef(checked.defs, defName)
  definitionTrustLines(d, checked.globals, checked.allDefs, declared,
    postulateTrust, runtimeTypes, initHashSet[string](), initHashSet[string]())

proc check(label: string, lines: seq[string], mustContain: seq[string],
           mustLack: seq[string]): bool {.compileTime.} =
  ## Returns true when all mustContain lines are present and all mustLack
  ## lines are absent. Prints the Trust section for inspection.
  echo label
  if lines.len == 0:
    echo "Trust: none"
  else:
    for line in lines:
      echo "Trust: " & line
  result = true
  for expected in mustContain:
    if expected notin lines:
      echo "FAIL: expected trust line missing: " & expected
      result = false
  for absent in mustLack:
    if absent in lines:
      echo "FAIL: unexpected trust line present: " & absent
      result = false
  echo (if result: "ok" else: "FAILED") & ": " & label

proc runChecks(): bool {.compileTime.} =
  result = true

  # Channel 1: imported definition calling a postulate. Block B declares
  # nothing; p lives in block A. The report must name p as a cross-block
  # boundary rather than staying silent.
  discard elabCheckDirStateAll(readFile(probeDir / "a.ep"), probeDir)
  let imported = elabCheckDirStateAll(readFile(probeDir / "b.ep"), probeDir)
  var boundTrust = initTable[string, string]()
  boundTrust["p"] = "bindPostulate(p, hostP): the Nim adapter behavior is trusted; its signature is checked"
  let externalLine = "postulate p: trust boundary declared in another block (reached through f)"
  result = check("channel 1: imported postulate is reported as cross-block",
    trustFor(imported, "g", initHashSet[string](), boundTrust, @[]),
    @[externalLine], @[]) and result
  # Realistic variant: B has no binding info at all; the external line must
  # still appear (the postulate is reachable, so silence would be a lie).
  result = check("channel 1: realistic empty bindings still report p",
    trustFor(imported, "g", initHashSet[string](), initTable[string, string](), @[]),
    @[externalLine], @[]) and result

  # Channel 2: type-level family application. KNOWN LIMITATION: the mapping
  # check is syntactic (it sees `F`, not the `Nat` that `F i` reduces to),
  # so the Nat mapping is absent. `i` is declared here to isolate the
  # mapping question from the cross-block postulate question.
  let typeLevel = elabCheckDirStateAll(readFile(probeDir / "type_level.ep"), probeDir)
  let natMapping = @[HostRuntimeType(eponymName: "Nat", nimType: ident"int")]
  var declaredI = initHashSet[string]()
  declaredI.incl("i")
  let natLine = "runtimeType(Nat, int): identity int representation; the Eponym/Nim correspondence is trusted"
  result = check("channel 2: type-level computation (known limitation)",
    trustFor(typeLevel, "g", declaredI, initTable[string, string](), natMapping),
    @[], @[natLine]) and result

  # Channel 3: callbacks. Both the higher-order postulate and the postulate
  # passed as callback must be reported.
  let callbacks = elabCheckDirStateAll(readFile(probeDir / "callbacks.ep"), probeDir)
  var declared = initHashSet[string]()
  declared.incl("apply")
  declared.incl("q")
  var callbackTrust = initTable[string, string]()
  callbackTrust["apply"] = "bindPostulateValue(apply, hostApply): the Nim adapter behavior is trusted; its signature is checked"
  callbackTrust["q"] = "bindPostulate(q, hostQ): the Nim adapter behavior is trusted; its signature is checked"
  result = check("channel 3: callbacks report both postulates",
    trustFor(callbacks, "g", declared, callbackTrust, @[]),
    @[callbackTrust["apply"], callbackTrust["q"]], @[]) and result

  # Channel 4: nested-representation codec. The codec used only inside
  # `Vec T n` must be reported. `t` is declared here to isolate the codec
  # question from the cross-block postulate question.
  let codec = elabCheckDirStateAll(readFile(probeDir / "nested_codec.ep"), probeDir)
  let codecMapping = @[HostRuntimeType(eponymName: "T", nimType: ident"TCodec",
    isRuntimeCodec: true, encoder: ident"encT", decoder: ident"decT")]
  var declaredT = initHashSet[string]()
  declaredT.incl("t")
  result = check("channel 4: nested codec is reported",
    trustFor(codec, "g", declaredT, initTable[string, string](), codecMapping),
    @["runtimeCodec(T, TCodec): custom encoder/decoder behavior is trusted"], @[]) and result

macro runProbes(): untyped =
  let ok = runChecks()
  if not ok:
    error("trust adversarial regression tests failed")

runProbes()
