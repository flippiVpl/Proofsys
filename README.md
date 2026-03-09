# Proofsys
Klonen: git clone --recurse-submodules <https://github.com/flippiVpl/Proofsys>

Dann Folgendes in dieser Reihenfolge ausführen:
mkdir build
cd build
cmake ..
cmake --build .

Der Code erwartet als ersten Parameter eine .nnf-Datei im Format von D4 und als zweiten die zugehörige .cnf-Datei. Der Aufruf kann also zum Beispiel folgendermaßen aussehen:
./proof test.nnf test.cnf