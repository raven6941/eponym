## Regression for generating Nat-aware opaque postulate adapters from the
## checked Eponym type identity and runtime representation mappings.

import eponym_mac
import eponym_embed

type Token = object
  value: int

type TaggedToken = object
  value: int

proc addToToken(amount: int, token: Token): Token =
  Token(value: token.value + amount)

proc tagToken(amount: int, token: Token): TaggedToken =
  TaggedToken(value: token.value + amount)

eponymBlock:
  postulate(Nat, Univ)
  postulate(zero, Nat)
  postulate(suc, Nat -> Nat)
  postulate(Token, Univ)
  postulate(TaggedToken, Univ)
  runtimeType(Token, Token)
  runtimeType(TaggedToken, TaggedToken)
  postulate(addToTokenPostulate, Nat -> Token -> Token)
  bindPostulate(addToTokenPostulate, addToToken, Nat, Token, Token)
  postulate(tagTokenPostulate, Nat -> Token -> TaggedToken)
  bindPostulate(tagTokenPostulate, tagToken, Nat, Token, TaggedToken)
  proc addToTokenChecked(amount: Nat, token: Token): Token =
    addToTokenPostulate(amount, token)
  proc tagTokenChecked(amount: Nat, token: Token): TaggedToken =
    tagTokenPostulate(amount, token)

when isMainModule:
  let got = addToTokenChecked(4, Token(value: 7))
  doAssert got.value == 11
  let tagged = tagTokenChecked(5, Token(value: 7))
  doAssert tagged.value == 12
  echo "test_nat_binding_identity: Nat adapter selected by checked identity"
