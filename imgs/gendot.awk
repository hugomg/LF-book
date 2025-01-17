$1 == "state" { for(i=2; i<=NF; i++) states[$i]=1; next;}
$1 == "start" { for(i=2; i<=NF; i++) starts[$i]=1; next;}
$1 == "final" { for(i=2; i<=NF; i++) finals[$i]=1; next;}

NF {
    nedges++;
    edgesrc[nedges] = $1;
    edgedst[nedges] = $2;
    edgelbl[nedges] = $3;
    next;
}


END {
    printf("digraph {\n")
    printf("  rankdir=LR;\n")
    printf("  edge [arrowsize=0.7];\n")

    printf("\n");

    for (q in starts) {
        printf("  beg%s [shape=none, label=\"\", height=0, width=0];\n", q);
    }

    for (q in states) {
        shape = (finals[q] ? "doublecircle" : "circle");
        printf("  %s [shape=%s];\n", q, shape);
    }

    printf("\n");

    for (q in starts) { printf("  beg%s -> %s;\n", q, q); }

    for (i=1; i<=nedges; i++) {
        printf("  %s -> %s [label=\"%s\"];\n", edgesrc[i], edgedst[i], edgelbl[i]);
    }

    printf("}\n");
}
