@FunDecl.sg_gen()
def fundecl_sg_gen(node, scope):
    scope.add_decl(node.name.text, node)
    return scope