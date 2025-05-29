# Верификация программ в .NET

## Цель
Сделать обзор темы “верификация программ”, продемонстрировать возможности языка Coq и показать, как код на Coq можно интегрировать в .NET-проекты.
Популяризировать F#.

## Аудитория
Программисты на C#, которые пишут приложения с повышенными требованиями к надёжности.
Программисты, которым нравится изучать новые интересные концепции.

## Содержание
* Война с ошибками
* Почему верификация?
* Сравниваем с code review.
* * `DbInterceptor`
* * Регистрация типа в Autofac
* Сравниваем с unit tests
  Пример с интервалом.
* Сравниваем c property based tests.
  Пример с быстрой сортировкой.
* В целом: ошибки в стандартных библиотеках
* Проблемы доказательства правильности
* * Чёрч и Тьюринг
* * Законы Моргана
* * Entscheidungsproblem
* * Proof assistants. Тактики. Язык Coq
* Насколько это серьёзно? Проблема четырёх красок
* Задача: рассчитываем ежемесячные начисления
* * Раскладываем задачу на составные части
* Воркшоп.
* * Простая функция. Индукция и рекурсия. Пример доказательства
* * Примеры тактик. Поиск готовых теорем
* * Извлечение в OCaml
* * OCaml == F#
* * Вызов F# из C#
* * Готовый пример
* Что ещё? Ссылки
* Где применять?
* Содержание

## Ссылки
* [Антон Стеканов, Евгений Каратаев. Введение в Coq](https://youtube.com/playlist?list=PLfkikHwnACaU3SFlJZ-fB2hZKppA6GfrM&si=qXOeQ1QAaNA1Wa9j)
* [ROCQ](https://rocq-prover.org/)
* [Software Foundations](https://softwarefoundations.cis.upenn.edu/)
* [COQ theorem prover online IDE](https://jscoq.github.io/scratchpad.html)
* [Towards formal verification of TLS network packet processing written in C](https://staff.aist.go.jp/reynald.affeldt/documents/plpv2013-affeldt-marti.pdf)
* [Verified Software Toolchain](https://vst.cs.princeton.edu/)
* [A computer-checked proof of the Four Colour Theorem](https://www2.tcs.ifi.lmu.de/~abel/lehre/WS07-08/CAFR/4colproof.pdf)
* [On the Worst-Case Complexity of TimSort](https://drops.dagstuhl.de/storage/00lipics/lipics-vol112-esa2018/LIPIcs.ESA.2018.4/LIPIcs.ESA.2018.4.pdf)
* [A bug was found in Java after almost 9 years of hiding](https://dev.to/matheusgomes062/a-bug-was-found-in-java-after-almost-9-years-of-hiding-2d4k)
