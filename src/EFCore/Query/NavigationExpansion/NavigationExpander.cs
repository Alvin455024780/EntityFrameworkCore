﻿// Copyright (c) .NET Foundation. All rights reserved.
// Licensed under the Apache License, Version 2.0. See License.txt in the project root for license information.

using System.Linq.Expressions;
using JetBrains.Annotations;
using Microsoft.EntityFrameworkCore.Infrastructure;
using Microsoft.EntityFrameworkCore.Metadata;
using Microsoft.EntityFrameworkCore.Query.NavigationExpansion.Visitors;
using Microsoft.EntityFrameworkCore.Utilities;

namespace Microsoft.EntityFrameworkCore.Query.NavigationExpansion
{
    public class NavigationExpander
    {
        private IModel _model;

        public NavigationExpander([NotNull] IModel model)
        {
            Check.NotNull(model, nameof(model));

            _model = model;
        }

        public virtual Expression ExpandNavigations(Expression expression)
        {
            var i = 0;
            if (i == 1)
            {
                return expression;
            }

            var newExpression = new NavigationExpandingVisitor(_model).Visit(expression);
            newExpression = new IncludeApplyingVisitor().Visit(newExpression);
            newExpression = new NavigationExpansionReducingVisitor().Visit(newExpression);

            // TODO: hack to workaround type discrepancy that can happen sometimes when rerwriting collection navigations
            return newExpression.RemoveConvert();
        }
    }
}
