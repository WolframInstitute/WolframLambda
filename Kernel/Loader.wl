Begin["Wolfram`Lambda`Loader`"]

SetDirectory[DirectoryName[$InputFileName]]

Get["Lambda.wl"]
Get["Compiled.wl"]


pacletInstalledQ[paclet_, version_] := AnyTrue[Through[PacletFind[paclet]["Version"]], ResourceFunction["VersionOrder"][#, version] <= 0 &]

Enclose[
    If[ ! pacletInstalledQ["Wolfram/DiagrammaticComputation", "1.0.6"],
        ConfirmMatch[PacletInstall["Wolfram/DiagrammaticComputation"], _PacletObject];
    ];
    Get["StringDiagram.wl"]
]

End[];