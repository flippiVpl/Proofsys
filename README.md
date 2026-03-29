# Proofsys
Empfohlenes Vorgehen zum bauen und ausführen:
```bash
git clone --recurse-submodules https://github.com/flippiVpl/Proofsys
cd Proofsys
mkdir build
cd build
cmake ..
cmake --build .
```

Der Code erwartet als ersten Parameter eine .nnf-Datei im Format von D4 und als zweiten die zugehörige .cnf-Datei. Der Aufruf kann also zum Beispiel folgendermaßen aussehen:

```bash
./proof test.nnf test.cnf
```

Im Verzeichnis Benchmarks sind die in der Arbeit erwähnten Tests aus der Model Counting Competiton bereitgestellt. Hinweis: Zum Testen müssen diese zuerst mit D4 kompiliert werden, sodass .nnf-Dateien entstehen.