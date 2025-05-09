`java -jar tla2tools.jar -config model$1.toolbox/Model_$1/MC.cfg model$1.tla -dump dot graph_model$1.dot`
`dot -Tsvg graph_model$1.dot > graph_model$1.svg`