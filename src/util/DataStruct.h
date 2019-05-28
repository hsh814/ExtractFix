//
// Created by gx on 28/05/19.
//

#ifndef CRASH_FREE_FIX_DATASTRUCT_H
#define CRASH_FREE_FIX_DATASTRUCT_H


struct Location {
    unsigned long fileId;
    unsigned long beginLine;
    unsigned long beginColumn;
    unsigned long endLine;
    unsigned long endColumn;

    bool operator==(const Location &other) const {
        return (fileId == other.fileId
                && beginLine == other.beginLine
                && beginColumn == other.beginColumn
                && endLine == other.endLine
                && endColumn == other.endColumn);
    }
};

#endif //CRASH_FREE_FIX_DATASTRUCT_H
