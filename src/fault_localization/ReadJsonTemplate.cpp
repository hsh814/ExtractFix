#include <iostream>
#include <fstream>
#include <jsoncpp/json/json.h>

using namespace std;

int main() {
    ifstream ifs("/tmp/fixlocations.json");
    Json::Reader reader;
    Json::Value obj;
    reader.parse(ifs, obj);     // Reader can also read strings
    for (int i = 0; i<obj.size(); i++){
        cout << "message: " << obj[i][0].asString() << endl;
        cout << "funcName: " << obj[i][1].asString() << endl;
        cout << "lineNo: " << obj[i][2].asString() << endl;
        Json::Value symVars = obj[i][3];
        cout << "symVars:";
        for (int j = 0; j<symVars.size(); j++)
            cout << " " << obj[i][3][j];
        cout << endl;
    }

    return 0;
}
