/*
 * File:  ackr_info.h
 * Author:  mikolas
 * Created on:  Mon, Nov 16, 2015 13:30:37
 * Copyright (C) 2015, Mikolas Janota
 */
#ifndef ACKR_INFO_H_12278
#define ACKR_INFO_H_12278
#include"obj_hashtable.h"
#include"ast.h"
class ackr_info {
    public:
        typedef obj_map<app, app*> t2ct;
        typedef obj_map<func_decl, app*> c2tt;

        inline app* find_term(func_decl* c)  const {
            app *  rv = 0;
            c2t.find(c,rv);
            return rv;
        }

        inline app* get_abstr(app* term)  const {
            app * const rv = t2c.find(term);
            SASSERT(rv);
            return rv;
        }

        inline void set_abstr(app* term, app* c) {
            SASSERT(c);
            t2c.insert(term,c);
            c2t.insert(c->get_decl(),term);
        }

        //inline const t2ct& get_map() const { return t2c; }
    private:
        t2ct t2c;
        c2tt c2t;
};
#endif /* ACKR_INFO_H_12278 */
