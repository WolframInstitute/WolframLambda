Begin["Wolfram`Lambda`Loader`"]

SetDirectory[DirectoryName[$InputFileName]]

Get["Lambda.wl"]
Get["Utilities.wl"]
Get["Enumeration.wl"]
Get["Evaluation.wl"]
Get["TreeGraphs.wl"]
Get["Visualization.wl"]
Get["Multiway.wl"]
Get["Compiled.wl"]
Get["EntityStore.wl"]


pacletInstalledQ[paclet_, version_] := AnyTrue[Through[PacletFind[paclet]["Version"]], ResourceFunction["VersionOrder"][#, version] <= 0 &]

Enclose[
    If[ ! pacletInstalledQ["Wolfram/DiagrammaticComputation", "1.0.7"],
        ConfirmMatch[PacletInstall["Wolfram/DiagrammaticComputation"], _PacletObject];
    ];
    Get["StringDiagram.wl"]
]

End[];