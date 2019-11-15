struct QObject {
  virtual ~QObject();
};

struct QFileInfoList : QObject {
  void *data;
  int count();
};

#define Q_FOREACH(variable,container) for (auto _container_ = QtPrivate::qMakeForeachContainer(container); _container_.control && _container_.i != _container_.e; ++_container_.i, _container_.control ^= 1) for (variable = *_container_.i; _container_.control; _container_.control = 0)
#define foreach Q_FOREACH

struct QString : QObject {
  void *data;
  QString operator+(const QString &rhs);
};

struct QFileInfo : QObject {
  void *data;
  QString absoluteFilePath();
  QString fileName();
};

struct QFile : QObject {
  void *data;
  static bool exists(QString name);
  static bool copy(QString, QString);
};

namespace QtPrivate {
  struct FEC {
    QFileInfo *i;
    QFileInfo *e;
    int control;
  };
  FEC qMakeForeachContainer(QFileInfoList &);
}

bool copyTempToProfile(QString tempPath, QString profilePath, bool * wasEmpty)
{
    bool was_empty = true;

    QFileInfoList files;
    if ( files.count() <= 0 )
        return false;

    int created = 0;
    foreach ( QFileInfo finfo, files)
    {
        QString tempFile = finfo.absoluteFilePath();
        QString profileFile = profilePath + finfo.fileName();

        //if ( ! profile_files_.contains(finfo.fileName()) )
        //{
        //    was_empty = false;
        //    continue;
        //}

        if ( ! QFile::exists(tempFile) || QFile::exists(profileFile) )
            continue;

        if ( QFile::copy(tempFile, profileFile) )
            created++;
    }

    if ( wasEmpty )
        *wasEmpty = was_empty;

    if ( created > 0 )
        return true;

    return false;
}
