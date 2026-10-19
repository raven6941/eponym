import eponym_mac

eponymBlock:
  import "returned_identity_factory.ep"
  postulate(Nat, Univ)

  proc legacyImportedFactory(value: Nat): Nat =
    importedIdentityFactory(unitv)(Nat, value)
