@FunctionDefinition.sg_gen()
def fundecl_sg_gen(node, scope):
    scope.add_decl(node.name.text, node)
    return scope

@Identifier.sg_gen()
def identifier_sg_gen(node, scope):
    scope.add_ref(node.text, node)
    return scope